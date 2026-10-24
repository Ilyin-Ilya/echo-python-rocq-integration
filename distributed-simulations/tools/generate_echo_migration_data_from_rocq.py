#!/usr/bin/env python3
"""Generate serialized generic Echo IR data for optional migration checks."""

from __future__ import annotations

import argparse
import hashlib
import pprint
import sys
from pathlib import Path
from typing import Sequence

REPOSITORY = Path(__file__).resolve().parent.parent
if str(REPOSITORY) not in sys.path:
    sys.path.insert(0, str(REPOSITORY))

from distributed_simulations.protocol_ir_codec import (
    decode_ir_capability_manifest,
)

if __package__:
    from . import rocq_codegen
    from .protocol_ir_descriptors import echo_descriptor
else:
    import rocq_codegen
    from protocol_ir_descriptors import echo_descriptor


def _validate_conformance_export(conformance: tuple) -> None:
    if (
        len(conformance) != 3
        or conformance[0] != "echo-conformance"
        or not isinstance(conformance[1], tuple)
        or len(conformance[1]) != 10
        or conformance[1][0] != "steps"
        or any(
            not isinstance(fixture, tuple)
            or len(fixture) != 6
            or fixture[0] != "step"
            for fixture in conformance[1][1:]
        )
        or not isinstance(conformance[2], tuple)
        or len(conformance[2]) != 2
        or conformance[2][0] != "runs"
        or not isinstance(conformance[2][1], tuple)
        or len(conformance[2][1]) != 6
        or conformance[2][1][0] != "run"
    ):
        raise rocq_codegen.GenerationError(
            "Echo conformance export must contain nine canonical steps and one run"
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rocq-project",
        type=Path,
        default=REPOSITORY.parent / "echo-algorithm-coq",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=REPOSITORY
        / "distributed_simulations"
        / "migration"
        / "generated_echo_program.py",
    )
    parser.add_argument("--coqtop")
    parser.add_argument("--rocqlib")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args(argv)

    try:
        rocq_project = arguments.rocq_project.resolve()
        theories = rocq_project / "theories"
        descriptor = echo_descriptor(theories)
        coqtop = rocq_codegen.find_coqtop(arguments.coqtop)
        rocqlib = rocq_codegen.find_rocqlib(arguments.rocqlib)
        envelope, source = rocq_codegen.evaluate_protocol_export(
            rocq_project=rocq_project,
            theories=theories,
            descriptor=descriptor,
            coqtop=coqtop,
            rocqlib=rocqlib,
            description="serialized generic Echo protocol IR migration data",
        )
        capability_source, conformance_source = rocq_codegen.evaluate_string_exports(
            rocq_project=rocq_project,
            theories=theories,
            logical_root=descriptor.logical_root,
            imports=descriptor.imports,
            exports=(
                rocq_codegen.RocqStringExport(
                    expression="ir_capability_manifest_sexpr",
                    compiled_module=theories / "ProtocolIRExport.vo",
                    sources=descriptor.export.sources,
                ),
                rocq_codegen.RocqStringExport(
                    expression="echo_ir_conformance_sexpr",
                    compiled_module=theories / "EchoIRExport.vo",
                    sources=descriptor.export.sources,
                ),
            ),
            coqtop=coqtop,
            rocqlib=rocqlib,
            description="generic Echo migration fixtures",
        )
        capability_manifest = rocq_codegen.parse_sexpr(capability_source)
        decode_ir_capability_manifest(
            capability_manifest,
            expected_schema_version=envelope.schema_version,
            expected_ir_version=envelope.ir_version,
        )
        conformance = rocq_codegen.parse_sexpr(conformance_source)
        _validate_conformance_export(conformance)
        rendered = rocq_codegen.render_protocol_data_module(
            envelope,
            source,
            generated_by="tools/generate_echo_migration_data_from_rocq.py",
        )
        rendered += (
            "\nIR_CAPABILITY_DIGEST = "
            f"{hashlib.sha256(capability_source.encode('utf-8')).hexdigest()!r}\n"
            "IR_CAPABILITY_TREE = "
            f"{pprint.pformat(capability_manifest, width=88, compact=False, sort_dicts=False)}\n"
            "\nROCQ_CONFORMANCE_DIGEST = "
            f"{hashlib.sha256(conformance_source.encode('utf-8')).hexdigest()!r}\n"
            "ROCQ_CONFORMANCE_TREE = "
            f"{pprint.pformat(conformance, width=88, compact=False, sort_dicts=False)}\n"
        )
        current = rocq_codegen.write_or_check(
            arguments.output.resolve(), rendered, arguments.check
        )
    except (rocq_codegen.GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if arguments.check and not current:
        print(
            f"error: serialized Echo migration data is stale: {arguments.output}",
            file=sys.stderr,
        )
        return 1
    action = "checked" if arguments.check else "generated"
    print(f"{action} serialized Echo migration data: {arguments.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
