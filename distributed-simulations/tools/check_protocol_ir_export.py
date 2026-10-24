#!/usr/bin/env python3
"""Validate the generic Rocq protocol-IR boundary with two protocols.

The counter fixture is intentionally not Echo-shaped.  Passing this check
shows that the shared transport can evaluate, parse, and validate versioned
counter and Echo programs without knowing either protocol's fields or rules.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path
from typing import Sequence

REPOSITORY = Path(__file__).resolve().parent.parent
if str(REPOSITORY) not in sys.path:
    sys.path.insert(0, str(REPOSITORY))

from distributed_simulations.protocol_ir_codec import (
    decode_exported_state,
    decode_ir_capability_manifest,
    decode_protocol_program,
    encode_exported_run_outcome,
    encode_exported_state,
)
from distributed_simulations.protocol_ir_interpreter import (
    initialize_protocol,
    interpret_step,
    make_config,
    make_delivery_event,
    make_start_event,
    run_schedule,
)
from distributed_simulations.protocol_values import RunStatus, StepSuccess

if __package__:
    from . import protocol_ir_python_compiler, rocq_codegen
    from .protocol_ir_descriptors import counter_descriptor, echo_descriptor
else:
    import protocol_ir_python_compiler
    import rocq_codegen
    from protocol_ir_descriptors import counter_descriptor, echo_descriptor


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rocq-project",
        type=Path,
        default=REPOSITORY.parent / "echo-algorithm-coq",
    )
    parser.add_argument("--coqtop")
    parser.add_argument("--rocqlib")
    arguments = parser.parse_args(argv)

    try:
        rocq_project = arguments.rocq_project.resolve()
        theories = rocq_project / "theories"
        coqtop = rocq_codegen.find_coqtop(arguments.coqtop)
        rocqlib = rocq_codegen.find_rocqlib(arguments.rocqlib)
        validated = []
        descriptors = (counter_descriptor(theories), echo_descriptor(theories))
        for descriptor in descriptors:
            envelope, source = rocq_codegen.evaluate_protocol_export(
                rocq_project=rocq_project,
                theories=theories,
                descriptor=descriptor,
                coqtop=coqtop,
                rocqlib=rocqlib,
                description=f"generic {descriptor.protocol_id} protocol IR",
            )
            program = decode_protocol_program(
                envelope.raw,
                node_decoder=int,
                expected_protocol_id=descriptor.protocol_id,
            )
            validated.append((envelope, source, program))

        # Execute the non-Echo fixture through the same decoder and interpreter
        # that will consume generated protocol data.  This checks typed natural
        # payloads and message references rather than merely parsing an envelope.
        counter_program = validated[0][2]
        counter_config = make_config(
            counter_program,
            nodes=(0,),
            neighbors={0: ()},
            fields={"initiator": 0},
        )
        start = make_start_event(counter_program, {"start-order": ()})
        delivery = make_delivery_event(
            counter_program, 1, {"expected-parent": None}
        )
        first = interpret_step(
            counter_program,
            counter_config,
            initialize_protocol(counter_program),
            start,
        )
        if not isinstance(first, StepSuccess) or first.rule_id != "start":
            raise RuntimeError(f"generic counter startup failed: {first!r}")
        second = interpret_step(
            counter_program, counter_config, first.state, delivery
        )
        if not isinstance(second, StepSuccess) or second.rule_id != "add":
            raise RuntimeError(f"generic counter delivery failed: {second!r}")
        outcome = run_schedule(
            counter_program, counter_config, 2, (start, delivery)
        )
        if outcome.status is not RunStatus.COMPLETE or outcome.steps != 2:
            raise RuntimeError(f"generic counter run failed: {outcome!r}")

        # Compile the second protocol to ordinary Python functions as well.
        # Executing this module in memory proves that the code-generation
        # backend is driven by the generic IR rather than Echo rule names.
        counter_source = validated[0][1]
        compiled_source = protocol_ir_python_compiler.render_compiled_module(
            counter_program,
            rocq_program_digest=hashlib.sha256(
                counter_source.encode("utf-8")
            ).hexdigest(),
            generated_by="tools/check_protocol_ir_export.py",
        )
        compiled_namespace = {}
        exec(
            compile(compiled_source, "<generated-counter>", "exec"),
            compiled_namespace,
        )
        compiled_config = compiled_namespace["make_config"](
            nodes=(0,), neighbors={0: ()}, fields={"initiator": 0}
        )
        compiled_start = compiled_namespace["make_start_event"](
            {"start-order": ()}
        )
        compiled_delivery = compiled_namespace["make_delivery_event"](
            1, {"expected-parent": None}
        )
        if compiled_config != counter_config:
            raise RuntimeError("compiled counter config constructor drifted")
        if compiled_start != start or compiled_delivery != delivery:
            raise RuntimeError("compiled counter event constructors drifted")
        compiled_first = compiled_namespace["step"](
            compiled_config,
            compiled_namespace["initialize_protocol"](),
            compiled_start,
        )
        if compiled_first != first:
            raise RuntimeError(
                "compiled counter startup differs from the generic interpreter"
            )
        compiled_second = compiled_namespace["step"](
            compiled_config, compiled_first.state, compiled_delivery
        )
        if compiled_second != second:
            raise RuntimeError(
                "compiled counter delivery differs from the generic interpreter"
            )
        compiled_scheduled_outcome = compiled_namespace["run_schedule"](
            compiled_config, 2, (compiled_start, compiled_delivery)
        )
        if compiled_scheduled_outcome != outcome:
            raise RuntimeError(
                "compiled counter schedule differs from the generic interpreter"
            )
        compiled_outcome = compiled_namespace["run_callback"](
            compiled_config,
            start_event=compiled_start,
            scheduler=lambda _state: 1,
            delivery_event=lambda _state, _message_id: compiled_delivery,
            max_steps=2,
        )
        if compiled_outcome != outcome:
            raise RuntimeError(
                "compiled counter run differs from the generic interpreter"
            )

        # Compare the Python result with protocol-neutral runtime values
        # computed and serialized by Rocq.  This is a cross-language semantic
        # check for the second protocol, not a handwritten expected-value test.
        counter_export = descriptors[0].export
        runtime_sources = rocq_codegen.evaluate_string_exports(
            rocq_project=rocq_project,
            theories=theories,
            logical_root=descriptors[0].logical_root,
            imports=descriptors[0].imports,
            exports=(
                rocq_codegen.RocqStringExport(
                    expression="ir_capability_manifest_sexpr",
                    compiled_module=counter_export.compiled_module,
                    sources=counter_export.sources,
                ),
                rocq_codegen.RocqStringExport(
                    expression="counter_initial_state_sexpr",
                    compiled_module=counter_export.compiled_module,
                    sources=counter_export.sources,
                ),
                rocq_codegen.RocqStringExport(
                    expression="counter_complete_run_sexpr",
                    compiled_module=counter_export.compiled_module,
                    sources=counter_export.sources,
                ),
            ),
            coqtop=coqtop,
            rocqlib=rocqlib,
            description="generic counter runtime conformance values",
        )
        capability_tree, expected_initial, expected_run = (
            rocq_codegen.parse_sexpr(source) for source in runtime_sources
        )
        decoded_capabilities = decode_ir_capability_manifest(
            capability_tree,
            expected_schema_version=validated[0][0].schema_version,
            expected_ir_version=validated[0][0].ir_version,
        )
        protocol_ir_python_compiler.validate_compiler_capabilities(
            decoded_capabilities
        )
        decoded_initial = decode_exported_state(
            counter_program, expected_initial, node_decoder=int
        )
        if expected_initial != encode_exported_state(decoded_initial, (0, 1)):
            raise RuntimeError("Python did not round-trip the Rocq counter initial state")
        if expected_initial != encode_exported_state(
            initialize_protocol(counter_program), (0, 1)
        ):
            raise RuntimeError("Python counter initial-state encoding differs from Rocq")
        if expected_run != encode_exported_run_outcome(outcome, (0, 1)):
            raise RuntimeError("Python counter complete run differs from Rocq")
    except (rocq_codegen.GenerationError, OSError, ValueError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    for envelope, source, _program in validated:
        digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
        print(
            f"validated {envelope.protocol_id} protocol IR envelope "
            f"(schema {envelope.schema_version}, IR {envelope.ir_version}, "
            f"digest {digest})"
        )
    print("validated exhaustive Rocq/interpreter/compiler capability manifest")
    print("matched generic counter initial state and complete run against Rocq")
    print("compiled the non-Echo counter IR to equivalent Python functions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
