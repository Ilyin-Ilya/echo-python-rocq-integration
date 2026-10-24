import unittest
from pathlib import Path

from distributed_simulations import protocol_compiled_runtime
from distributed_simulations.algorithms import generated_echo_executable
from distributed_simulations.protocol_values import (
    FieldDeclaration,
    IRType,
    ProtocolIRValidationError,
)


class CompiledEchoTests(unittest.TestCase):
    def test_generated_runtime_contract_is_current(self):
        self.assertEqual(
            protocol_compiled_runtime.COMPILED_RUNTIME_ABI_VERSION,
            generated_echo_executable.RUNTIME_ABI_VERSION,
        )
        self.assertEqual(
            protocol_compiled_runtime.GENERATED_PROTOCOL_API_VERSION,
            generated_echo_executable.GENERATED_API_VERSION,
        )
        self.assertEqual(
            protocol_compiled_runtime.GENERATED_PROTOCOL_PUBLIC_NAMES,
            generated_echo_executable.__all__,
        )

    def test_generated_signature_constructors_reject_adapter_drift(self):
        self.assertEqual(
            (FieldDeclaration("initiator", IRType.NODE),),
            generated_echo_executable.CONFIG_FIELDS,
        )
        self.assertEqual((), generated_echo_executable.START_CERTIFICATE_FIELDS)
        self.assertEqual((), generated_echo_executable.DELIVERY_CERTIFICATE_FIELDS)
        with self.assertRaises(ProtocolIRValidationError):
            generated_echo_executable.make_config(
                nodes=(0,), neighbors={0: ()}, fields={}
            )
        with self.assertRaises(ProtocolIRValidationError):
            generated_echo_executable.make_start_event({"unexpected": 1})
        with self.assertRaises(ProtocolIRValidationError):
            generated_echo_executable.make_delivery_event(-1, {})

    def test_compiled_schedule_runner_validates_fuel(self):
        config = generated_echo_executable.make_config(
            nodes=(0,), neighbors={0: ()}, fields={"initiator": 0}
        )
        for invalid in (-1, True):
            with self.subTest(fuel=invalid):
                with self.assertRaises(ProtocolIRValidationError):
                    generated_echo_executable.run_schedule(config, invalid, ())

    def test_generated_executable_does_not_interpret_protocol_tree(self):
        source = Path(generated_echo_executable.__file__).read_text(encoding="utf-8")
        self.assertIn("from distributed_simulations.protocol_values import", source)
        self.assertNotIn("from distributed_simulations.protocol_ir import", source)
        self.assertNotIn("PROTOCOL_TREE", source)
        self.assertNotIn("interpret_step", source)
        self.assertNotIn("evaluate_expression", source)
        self.assertNotIn("evaluate_action", source)

    def test_generated_rules_expose_readable_named_values(self):
        source = Path(generated_echo_executable.__file__).read_text(encoding="utf-8")
        self.assertIn("message = runtime.message_for(event)", source)
        self.assertIn("sender = message.sender", source)
        self.assertIn("receiver = message.receiver", source)
        self.assertIn("def _config_initiator(config):", source)
        self.assertIn("def _local_parent(state, node):", source)
        self.assertIn("def _set_local_parent(state, node, value):", source)
        self.assertIn("guard_receiver_is_not_initiator =", source)
        self.assertIn("guard_parent_is_none =", source)
        self.assertIn("forwarding_targets =", source)
        self.assertIn("parent_node = receiver", source)
        self.assertIn("parent_value = sender", source)
        self.assertNotIn("guard_1 =", source)
        self.assertNotIn("process_1 =", source)
        self.assertNotIn("value_1 =", source)

    def test_generated_predicates_use_named_conditions(self):
        source = Path(generated_echo_executable.__file__).read_text(encoding="utf-8")
        self.assertIn("message_queue_is_empty =", source)
        self.assertIn("pending_is_empty =", source)
        self.assertIn("finished_or_initiator_neighbors_is_empty =", source)

    def test_generated_echo_has_certificate_free_event_conveniences(self):
        start = generated_echo_executable.start_event()
        delivery = generated_echo_executable.deliver(1)
        self.assertEqual((), start.certificates)
        self.assertEqual((), delivery.certificates)

    def test_generated_step_uses_a_readable_rule_table(self):
        source = Path(generated_echo_executable.__file__).read_text(encoding="utf-8")
        self.assertIn("_RULES = (", source)
        self.assertIn("for rule_id, check, action in _RULES:", source)

    def test_production_and_trace_paths_do_not_load_protocol_tree(self):
        algorithms = Path(generated_echo_executable.__file__).parent
        for name in (
            "echo.py",
            "echo_codec.py",
            "echo_execution.py",
            "echo_trace.py",
        ):
            source = (algorithms / name).read_text(encoding="utf-8")
            with self.subTest(module=name):
                self.assertNotIn("generated_echo_program", source)
                self.assertNotIn("load_echo_program", source)
                self.assertNotIn("PROTOCOL_TREE", source)
                self.assertNotIn("interpret_step", source)
                self.assertNotIn("protocol_ir import", source)

        runtime_source = (
            algorithms.parent / "protocol_compiled_runtime.py"
        ).read_text(encoding="utf-8")
        self.assertIn("from .protocol_values import", runtime_source)
        self.assertNotIn("from .protocol_ir import", runtime_source)

        values_source = (algorithms.parent / "protocol_values.py").read_text(
            encoding="utf-8"
        )
        self.assertNotIn("def interpret_step", values_source)
        self.assertNotIn("def evaluate_expression", values_source)

    def test_public_echo_runner_keeps_scheduling_and_tracing_outside(self):
        algorithms = Path(generated_echo_executable.__file__).parent
        source = (algorithms / "echo.py").read_text(encoding="utf-8")
        self.assertNotIn("random.Random", source)
        self.assertNotIn("EventLog", source)
        self.assertIn("execute_generated_echo", source)

if __name__ == "__main__":
    unittest.main()
