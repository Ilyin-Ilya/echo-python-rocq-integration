#!/usr/bin/env python3
"""Generate the production Echo Python executable from the Rocq IR program."""

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
    decode_ir_capability_manifest,
    decode_protocol_program,
)

if __package__:
    from . import protocol_ir_python_compiler, rocq_codegen
    from .protocol_ir_descriptors import echo_descriptor
else:
    import rocq_codegen
    import protocol_ir_python_compiler
    from protocol_ir_descriptors import echo_descriptor


def main(argv: Sequence[str] | None = None) -> int:
    repository = REPOSITORY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rocq-project",
        type=Path,
        default=repository.parent / "echo-algorithm-coq",
    )
    parser.add_argument(
        "--executable-output",
        type=Path,
        default=repository
        / "distributed_simulations"
        / "algorithms"
        / "generated_echo_executable.py",
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
            description="data-only generic Echo protocol IR",
        )
        (capability_source,) = rocq_codegen.evaluate_string_exports(
            rocq_project=rocq_project,
            theories=theories,
            logical_root=descriptor.logical_root,
            imports=descriptor.imports,
            exports=(rocq_codegen.RocqStringExport(
                expression="ir_capability_manifest_sexpr",
                compiled_module=theories / "ProtocolIRExport.vo",
                sources=descriptor.export.sources,
            ),),
            coqtop=coqtop,
            rocqlib=rocqlib,
            description="generic IR compiler capabilities",
        )
        capability_manifest = rocq_codegen.parse_sexpr(capability_source)
        decoded_capabilities = decode_ir_capability_manifest(
            capability_manifest,
            expected_schema_version=envelope.schema_version,
            expected_ir_version=envelope.ir_version,
        )
        protocol_ir_python_compiler.validate_compiler_capabilities(
            decoded_capabilities
        )
        program = decode_protocol_program(
            envelope.raw,
            node_decoder=int,
            expected_protocol_id=envelope.protocol_id,
            expected_schema_version=envelope.schema_version,
            expected_ir_version=envelope.ir_version,
        )
        executable = protocol_ir_python_compiler.render_compiled_module(
            program,
            rocq_program_digest=hashlib.sha256(
                source.encode("utf-8")
            ).hexdigest(),
            generated_by="tools/generate_echo_program_from_rocq.py",
        )
        current = rocq_codegen.write_or_check(
            arguments.executable_output.resolve(), executable, arguments.check
        )
    except (rocq_codegen.GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if arguments.check and not current:
        print(
            "error: generated Echo executable is stale: "
            f"{arguments.executable_output}",
            file=sys.stderr,
        )
        return 1
    action = "checked" if arguments.check else "generated"
    print(f"{action} production Echo executable: {arguments.executable_output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
