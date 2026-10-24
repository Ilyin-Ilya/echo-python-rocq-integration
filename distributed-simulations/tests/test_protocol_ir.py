import re
import unittest
from dataclasses import replace
from pathlib import Path

from distributed_simulations import protocol_compiled_runtime
from distributed_simulations.protocol_ir_ast import (
    SUPPORTED_ACTION_CONSTRUCTORS,
    SUPPORTED_EVENT_PATTERNS,
    SUPPORTED_EXPRESSION_CONSTRUCTORS,
)
from distributed_simulations.protocol_ir_codec import (
    decode_ir_capability_manifest,
    decode_protocol_program,
)
from distributed_simulations.protocol_ir_interpreter import (
    initialize_protocol,
    interpret_step,
    make_config,
    make_delivery_event,
    make_start_event,
    run_callback,
    run_schedule,
    runtime_contract,
)
from distributed_simulations.protocol_values import (
    DeliveryEvent,
    IRType,
    IRValue,
    ProtocolIRValidationError,
    RunStatus,
    StepError,
    StepFailure,
    StepSuccess,
    StartEvent,
)
from tools.rocq_codegen import parse_sexpr
from tools.protocol_ir_python_compiler import (
    CompilationError,
    render_compiled_module,
    validate_compiler_capabilities,
)


COUNTER_EXPORT = """(protocol-ir
  (schema-version 1)
  (ir-version 1)
  (protocol-id counter)
  (signature
    (local-fields (field seen bool) (field parent option-node))
    (global-fields (field started bool) (field total nat))
    (config-fields (field initiator node))
    (message-kinds add done)
    (payload-fields (field amount nat) (field cause message-ref))
    (start-certificate-fields (field start-order list-node))
    (delivery-certificate-fields (field expected-parent option-node))
    (rule-ids start add done))
  (program
    (initial
      (local-fields
        (field seen (bool false))
        (field parent (option-node none)))
      (global-fields
        (field started (bool false))
        (field total (nat 0)))
      (next-message-id 1))
    (rules
      (rule start start (guards)
        (sequence
          (set-global started (literal (bool true)))
          (emit add (config initiator) (config initiator)
            (payload
              (field amount (literal (nat 5)))
              (field cause (literal (message-ref 0)))))))
      (rule add (deliver add)
        (guards (equal message-receiver (config initiator)))
        (sequence
          (set-global total (nat-add (global total) (payload amount)))
          remove-selected-message)))
    (complete
      (and (equal (global total) (literal (nat 5))) message-store-empty))
    (stuck
      (and (global started)
        (and
          (not (and
            (equal (global total) (literal (nat 5)))
            message-store-empty))
          message-store-empty)))))"""

COUNTER_TEST_DIGEST = "0" * 64
CAPABILITY_MANIFEST = (
    "protocol-ir-capabilities",
    ("schema-version", "1"),
    ("ir-version", "1"),
    ("types", *(kind.value for kind in IRType)),
    ("expressions", *SUPPORTED_EXPRESSION_CONSTRUCTORS),
    ("actions", *SUPPORTED_ACTION_CONSTRUCTORS),
    ("event-patterns", *SUPPORTED_EVENT_PATTERNS),
)


class CapabilityManifestTests(unittest.TestCase):
    def test_generated_rocq_capabilities_match_python_runtime(self):
        manifest = decode_ir_capability_manifest(
            CAPABILITY_MANIFEST,
            expected_schema_version=1,
            expected_ir_version=1,
        )

        self.assertEqual(tuple(kind.value for kind in IRType), manifest.types)
        self.assertEqual(SUPPORTED_EXPRESSION_CONSTRUCTORS, manifest.expressions)
        self.assertEqual(SUPPORTED_ACTION_CONSTRUCTORS, manifest.actions)
        self.assertEqual(SUPPORTED_EVENT_PATTERNS, manifest.event_patterns)
        validate_compiler_capabilities(manifest)

    def test_capability_drift_is_rejected_before_program_execution(self):
        manifest = CAPABILITY_MANIFEST
        expressions = manifest[4]
        missing_constructor = (
            *manifest[:4],
            ("expressions", *expressions[1:-1]),
            *manifest[5:],
        )

        with self.assertRaisesRegex(
            ProtocolIRValidationError, "Rocq/Python IR capability mismatch"
        ):
            decode_ir_capability_manifest(missing_constructor)

    def test_direct_compiler_rejects_capability_drift(self):
        manifest = decode_ir_capability_manifest(
            CAPABILITY_MANIFEST,
            expected_schema_version=1,
            expected_ir_version=1,
        )
        missing = replace(
            manifest,
            expressions=manifest.expressions + ("future-expression",),
        )
        with self.assertRaisesRegex(
            CompilationError,
            "direct compiler capability mismatch",
        ):
            validate_compiler_capabilities(missing)


class ProtocolIRTests(unittest.TestCase):
    def setUp(self):
        self.program = decode_protocol_program(
            parse_sexpr(COUNTER_EXPORT),
            node_decoder=int,
            expected_protocol_id="counter",
        )
        self.config = make_config(
            self.program,
            nodes=(0,),
            neighbors={0: ()},
            fields={"initiator": 0},
        )
        self.start = make_start_event(self.program, {"start-order": ()})
        self.delivery = make_delivery_event(
            self.program, 1, {"expected-parent": None}
        )

    def test_decoder_preserves_typed_signature(self):
        self.assertEqual("counter", self.program.protocol_id)
        self.assertEqual(2, len(self.program.rules))
        self.assertEqual(
            (IRType.NAT, IRType.MESSAGE_REF),
            tuple(field.kind for field in self.program.signature.payload_fields),
        )

    def test_runtime_contract_exposes_hooks_but_not_rule_authority(self):
        contract = runtime_contract(self.program)

        self.assertEqual("counter", contract.protocol_id)
        self.assertEqual(
            ("initiator",), tuple(field.name for field in contract.config_fields)
        )
        self.assertEqual(
            ("start-order",),
            tuple(field.name for field in contract.start_certificate_fields),
        )
        self.assertEqual(
            ("expected-parent",),
            tuple(field.name for field in contract.delivery_certificate_fields),
        )
        self.assertEqual(("add", "done"), contract.message_kinds)
        self.assertEqual(
            ("amount", "cause"),
            tuple(field.name for field in contract.payload_fields),
        )
        self.assertEqual(
            ("start", "add", "done"), contract.diagnostic_rule_ids
        )
        self.assertNotIn("rule", run_callback.__annotations__)

    def test_counter_executes_start_and_delivery(self):
        first = interpret_step(
            self.program,
            self.config,
            initialize_protocol(self.program),
            self.start,
        )
        self.assertIsInstance(first, StepSuccess)
        self.assertEqual("start", first.rule_id)
        self.assertEqual(1, len(first.state.messages))
        self.assertEqual(5, first.state.messages[0].payload[0][1].value)

        second = interpret_step(
            self.program, self.config, first.state, self.delivery
        )
        self.assertIsInstance(second, StepSuccess)
        self.assertEqual("add", second.rule_id)
        self.assertEqual((), second.state.messages)
        self.assertEqual(5, dict(second.state.globals)["total"].value)

    def test_counter_compiles_to_equivalent_python_functions(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        namespace = {}
        exec(compile(source, "<compiled-counter-test>", "exec"), namespace)

        interpreted_first = interpret_step(
            self.program,
            self.config,
            initialize_protocol(self.program),
            self.start,
        )
        compiled_first = namespace["step"](
            self.config,
            namespace["initialize_protocol"](),
            self.start,
        )
        self.assertEqual(interpreted_first, compiled_first)

        interpreted_second = interpret_step(
            self.program,
            self.config,
            interpreted_first.state,
            self.delivery,
        )
        compiled_second = namespace["step"](
            self.config,
            compiled_first.state,
            self.delivery,
        )
        self.assertEqual(interpreted_second, compiled_second)

    def test_generated_module_rejects_an_incompatible_runtime_abi(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        current = protocol_compiled_runtime.COMPILED_RUNTIME_ABI_VERSION
        incompatible = source.replace(
            f"RUNTIME_ABI_VERSION = {current}",
            f"RUNTIME_ABI_VERSION = {current + 1}",
            1,
        )
        self.assertNotEqual(source, incompatible)
        with self.assertRaisesRegex(
            protocol_compiled_runtime.CompiledRuntimeCompatibilityError,
            "requires compiled-runtime ABI",
        ):
            exec(
                compile(incompatible, "<incompatible-counter>", "exec"),
                {},
            )

    def test_generated_module_rejects_an_incomplete_public_api(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        incomplete = source.replace(
            "def run_schedule(config, fuel, schedule, state=None):",
            "def omitted_run_schedule(config, fuel, schedule, state=None):",
            1,
        )
        self.assertNotEqual(source, incomplete)
        with self.assertRaisesRegex(
            protocol_compiled_runtime.GeneratedProtocolInterfaceError,
            "invalid generated protocol interface",
        ):
            exec(
                compile(incomplete, "<incomplete-counter>", "exec"),
                {},
            )

    def test_generated_module_rejects_public_signature_drift(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        drifted = source.replace(
            "def run_schedule(config, fuel, schedule, state=None):",
            "def run_schedule(config, fuel, schedule):",
            1,
        )
        self.assertNotEqual(source, drifted)
        with self.assertRaisesRegex(
            protocol_compiled_runtime.GeneratedProtocolInterfaceError,
            "generated protocol signature mismatch",
        ):
            exec(
                compile(drifted, "<signature-drifted-counter>", "exec"),
                {},
            )

    def test_generated_module_rejects_invalid_metadata(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        invalid = source.replace(
            f"ROCQ_PROGRAM_DIGEST = {COUNTER_TEST_DIGEST!r}",
            "ROCQ_PROGRAM_DIGEST = 'not-a-sha256-digest'",
            1,
        )
        self.assertNotEqual(source, invalid)
        with self.assertRaisesRegex(
            protocol_compiled_runtime.GeneratedProtocolInterfaceError,
            "invalid generated protocol metadata",
        ):
            exec(
                compile(invalid, "<invalid-metadata-counter>", "exec"),
                {},
            )

    def test_compiled_schedule_runner_matches_every_interpreter_outcome(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        namespace = {}
        exec(compile(source, "<compiled-counter-test>", "exec"), namespace)

        initial = initialize_protocol(self.program)
        started = interpret_step(
            self.program, self.config, initial, self.start
        )
        self.assertIsInstance(started, StepSuccess)
        stuck = replace(started.state, messages=())
        malformed = replace(initial, globals=())
        cases = (
            ("complete", 2, (self.start, self.delivery), None),
            ("bounded", 0, (self.start, self.delivery), None),
            ("schedule-exhausted", 2, (), None),
            ("rejected-step", 1, (self.delivery,), None),
            ("stuck", 1, (), stuck),
            ("malformed-predicate", 1, (), malformed),
        )
        for name, fuel, schedule, state in cases:
            with self.subTest(outcome=name):
                interpreted = run_schedule(
                    self.program,
                    self.config,
                    fuel,
                    schedule,
                    state,
                )
                compiled = namespace["run_schedule"](
                    self.config, fuel, schedule, state
                )
                self.assertEqual(interpreted, compiled)

    def test_compiled_callback_runner_matches_interpreter_boundaries(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        namespace = {}
        exec(compile(source, "<compiled-counter-test>", "exec"), namespace)

        def interpreted(scheduler, max_steps=10_000):
            return run_callback(
                self.program,
                self.config,
                start_event=self.start,
                scheduler=scheduler,
                delivery_event=lambda _state, message_id: make_delivery_event(
                    self.program,
                    message_id,
                    {"expected-parent": None},
                ),
                max_steps=max_steps,
            )

        def compiled(scheduler, max_steps=10_000):
            return namespace["run_callback"](
                self.config,
                start_event=self.start,
                scheduler=scheduler,
                delivery_event=lambda _state, message_id: make_delivery_event(
                    self.program,
                    message_id,
                    {"expected-parent": None},
                ),
                max_steps=max_steps,
            )

        schedulers = (
            ("complete", lambda state: state.messages[0].identifier, 2),
            ("bounded", lambda state: state.messages[0].identifier, 0),
            ("rejected", lambda _state: 99, 2),
        )
        for name, scheduler, max_steps in schedulers:
            with self.subTest(outcome=name):
                self.assertEqual(
                    interpreted(scheduler, max_steps),
                    compiled(scheduler, max_steps),
                )

        for invalid in (-1, True):
            with self.subTest(invalid_max_steps=invalid):
                with self.assertRaises(ProtocolIRValidationError):
                    interpreted(lambda _state: 1, invalid)
                with self.assertRaises(ProtocolIRValidationError):
                    compiled(lambda _state: 1, invalid)

    def test_generic_runner_matches_two_step_counter_run(self):
        outcome = run_schedule(
            self.program,
            self.config,
            2,
            (self.start, self.delivery),
        )
        self.assertIs(RunStatus.COMPLETE, outcome.status)
        self.assertEqual(2, outcome.steps)
        self.assertEqual(5, dict(outcome.state.globals)["total"].value)

    def test_callback_runner_confines_scheduler_to_message_identity(self):
        observations = []
        outcome = run_callback(
            self.program,
            self.config,
            start_event=self.start,
            scheduler=lambda state: state.messages[0].identifier,
            delivery_event=lambda _state, message_id: make_delivery_event(
                self.program,
                message_id,
                {"expected-parent": None},
            ),
            observer=lambda state, steps, event: observations.append(
                (state, steps, event)
            ),
        )

        self.assertIs(RunStatus.COMPLETE, outcome.status)
        self.assertEqual(2, outcome.steps)
        self.assertEqual(3, len(observations))
        self.assertIsNone(observations[0][2])
        self.assertEqual(5, dict(outcome.state.globals)["total"].value)

    def test_callback_runner_rejects_an_unqueued_scheduler_choice(self):
        outcome = run_callback(
            self.program,
            self.config,
            start_event=self.start,
            scheduler=lambda _state: 99,
            delivery_event=lambda _state, message_id: make_delivery_event(
                self.program,
                message_id,
                {"expected-parent": None},
            ),
        )

        self.assertIs(RunStatus.INVALID, outcome.status)
        self.assertEqual("transition-rejected:unqueued-message", outcome.error)

    def test_unqueued_delivery_is_rejected(self):
        event = make_delivery_event(
            self.program, 99, {"expected-parent": None}
        )
        result = interpret_step(
            self.program,
            self.config,
            initialize_protocol(self.program),
            event,
        )
        self.assertEqual(StepFailure(StepError.UNQUEUED_MESSAGE), result)

    def test_step_revalidates_directly_constructed_external_events(self):
        source = render_compiled_module(
            self.program,
            rocq_program_digest=COUNTER_TEST_DIGEST,
            generated_by="tests/test_protocol_ir.py",
        )
        namespace = {}
        exec(compile(source, "<compiled-counter-test>", "exec"), namespace)

        interpreted_started = interpret_step(
            self.program,
            self.config,
            initialize_protocol(self.program),
            self.start,
        )
        compiled_started = namespace["step"](
            self.config,
            namespace["initialize_protocol"](),
            self.start,
        )
        self.assertIsInstance(interpreted_started, StepSuccess)
        self.assertIsInstance(compiled_started, StepSuccess)

        boolean_id = DeliveryEvent(True, self.delivery.certificates)
        malformed_start = StartEvent(
            (("start-order", IRValue(IRType.NAT, 0)),)
        )
        for name, event, interpreted_state, compiled_state in (
            (
                "boolean-message-id",
                boolean_id,
                interpreted_started.state,
                compiled_started.state,
            ),
            (
                "mistyped-start-certificate",
                malformed_start,
                initialize_protocol(self.program),
                namespace["initialize_protocol"](),
            ),
        ):
            with self.subTest(event=name):
                with self.assertRaises(ProtocolIRValidationError):
                    interpret_step(
                        self.program, self.config, interpreted_state, event
                    )
                with self.assertRaises(ProtocolIRValidationError):
                    namespace["step"](
                        self.config, compiled_state, event
                    )

    def test_ambiguous_rules_are_rejected(self):
        ambiguous = replace(
            self.program,
            rules=(self.program.rules[0], self.program.rules[0])
            + self.program.rules[1:],
        )
        result = interpret_step(
            ambiguous,
            self.config,
            initialize_protocol(ambiguous),
            self.start,
        )
        self.assertEqual(StepFailure(StepError.AMBIGUOUS_ENABLED_RULES), result)

    def test_decoder_rejects_unknown_expression_constructor(self):
        invalid = COUNTER_EXPORT.replace(
            "(nat-add (global total) (payload amount))",
            "(subtract (global total) (payload amount))",
        )
        with self.assertRaises(ProtocolIRValidationError):
            decode_protocol_program(parse_sexpr(invalid), node_decoder=int)

    def test_decoder_rejects_constructor_arity_type_and_identifier_mutations(self):
        invalid_exports = (
            COUNTER_EXPORT.replace(
                "(literal (nat 5))", "(literal (nat 5) extra)"
            ),
            COUNTER_EXPORT.replace(
                "(field amount nat)", "(field amount bool)"
            ),
            COUNTER_EXPORT.replace(
                "(rule start start", "(rule unknown start"
            ),
        )
        for invalid in invalid_exports:
            with self.subTest(invalid=invalid):
                with self.assertRaises(ProtocolIRValidationError):
                    decode_protocol_program(parse_sexpr(invalid), node_decoder=int)

    def test_runtime_certificates_are_exact_and_typed(self):
        with self.assertRaises(ProtocolIRValidationError):
            make_start_event(self.program, {})
        with self.assertRaises(ProtocolIRValidationError):
            make_start_event(self.program, {"start-order": 4})


class EchoArchitectureBoundaryTests(unittest.TestCase):
    def test_production_echo_path_does_not_import_migration_oracles(self):
        package = (
            Path(__file__).resolve().parents[1]
            / "distributed_simulations"
            / "algorithms"
        )
        production_modules = (
            package / "echo.py",
            package / "echo_codec.py",
            package / "echo_execution.py",
            package / "echo_trace.py",
            package / "echo_explorer.py",
        )
        for module in production_modules:
            with self.subTest(module=module.name):
                source = module.read_text(encoding="utf-8")
                self.assertNotIn("generated_echo_core", source)
                self.assertNotIn("generated_echo_oracles", source)

    def test_public_rocq_echo_api_is_legacy_free(self):
        theories = Path(__file__).resolve().parents[2] / "echo-algorithm-coq" / "theories"
        public_boundary = (
            theories / "EchoIRConfig.v",
            theories / "EchoIRExecutable.v",
            theories / "EchoIRExecutableInvariants.v",
            theories / "EchoIRExecutableLifecycle.v",
            theories / "EchoIRExecutablePending.v",
            theories / "EchoIRExecutableDiscovery.v",
            theories / "EchoIRExecutableTopology.v",
            theories / "EchoIRExecutableRequestAccounting.v",
            theories / "EchoIRExecutableRequestParent.v",
            theories / "EchoIRExecutableReplyDiscovery.v",
            theories / "EchoIRExecutableRequestReply.v",
            theories / "EchoIRExecutableObligations.v",
            theories / "EchoIRExecutableSpanningTree.v",
            theories / "EchoIRSpanningTree.v",
            theories / "EchoIRSpanningTreeExamples.v",
            theories / "EchoIRSafety.v",
            theories / "EchoIRAccounting.v",
            theories / "EchoIRObligations.v",
            theories / "EchoIRExecutableExamples.v",
            theories / "EchoIRExport.v",
        )
        forbidden = (
            "EchoTransitionIR",
            "EchoIRCompatibility",
            "EchoIRForwardSimulation",
            "EchoIRBackwardSimulation",
        )
        for module in public_boundary:
            source = module.read_text(encoding="utf-8")
            imported_modules = " ".join(
                re.findall(r"Require Import\s+(.*?)\.", source, flags=re.DOTALL)
            )
            for dependency in forbidden:
                with self.subTest(module=module.name, dependency=dependency):
                    self.assertNotIn(dependency, imported_modules)

    def test_direct_ir_spanning_tree_theorem_is_present(self):
        theorem_file = (
            Path(__file__).resolve().parents[2]
            / "echo-algorithm-coq"
            / "theories"
            / "EchoIRExecutableSpanningTree.v"
        )
        source = theorem_file.read_text(encoding="utf-8")
        self.assertIn("Theorem EchoStep_preserves_discovery_frontier", source)
        self.assertIn("Theorem echo_reachable_discovery_frontier", source)
        self.assertIn(
            "Theorem echo_reachable_finished_root_spanning_tree", source
        )

    def test_migration_stack_is_outside_the_maintained_rocq_build(self):
        rocq_root = Path(__file__).resolve().parents[2] / "echo-algorithm-coq"
        maintained = (rocq_root / "_CoqProject").read_text(encoding="utf-8")
        migration = (rocq_root / "_CoqProject.migration").read_text(
            encoding="utf-8"
        )
        migration_files = (
            "theories/LTS.v",
            "theories/Network.v",
            "theories/EchoAlgorithm.v",
            "theories/EchoCorrectness.v",
            "theories/Example.v",
            "theories/EchoExecutableTypes.v",
            "theories/EchoExecutableDecision.v",
            "theories/EchoExecutableAbstraction.v",
            "theories/EchoTransitionIR.v",
            "theories/EchoExecutableReachability.v",
            "theories/EchoExecutableTopology.v",
            "theories/EchoExecutableLifecycle.v",
            "theories/EchoExecutablePending.v",
            "theories/EchoExecutableCompletion.v",
            "theories/EchoExecutableForest.v",
            "theories/EchoExecutableDiscovery.v",
            "theories/EchoExecutableRequestAccounting.v",
            "theories/EchoExecutableObligations.v",
            "theories/EchoExecutablePostDecision.v",
            "theories/EchoRunner.v",
            "theories/EchoRunnerExamples.v",
            "theories/EchoTransitionIRExport.v",
            "theories/EchoExecutableRefinement.v",
            "theories/EchoExecutableCorrect.v",
            "theories/EchoExecutableExamples.v",
            "theories/EchoEvaluationVectorsExport.v",
            "theories/EchoRunnerVectorsExport.v",
            "theories/EchoExecutableSpanningTree.v",
            "theories/EchoExecutableSpanningTreeExamples.v",
        )
        retired_exact_state_files = (
            "theories/EchoIRCompatibility.v",
            "theories/EchoIRForwardSimulation.v",
            "theories/EchoIRBackwardSimulation.v",
            "theories/EchoIRProgramExamples.v",
        )
        self.assertIn("theories/EchoTopology.v", maintained)
        self.assertNotIn("theories/EchoTopology.v", migration)
        for migration_file in migration_files:
            with self.subTest(migration_file=migration_file):
                self.assertNotIn(migration_file, maintained)
                self.assertIn(migration_file, migration)
        for retired_file in retired_exact_state_files:
            with self.subTest(retired_file=retired_file):
                self.assertNotIn(retired_file, maintained)
                self.assertNotIn(retired_file, migration)
                self.assertTrue((rocq_root / retired_file).is_file())

if __name__ == "__main__":
    unittest.main()
