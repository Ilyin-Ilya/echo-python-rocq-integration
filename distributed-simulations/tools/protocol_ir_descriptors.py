"""Formal export descriptors used by generic-IR generation commands."""

from pathlib import Path

if __package__:
    from . import rocq_codegen
else:
    import rocq_codegen


GENERIC_MODULES = (
    "ProtocolIRTypes.v",
    "ProtocolIRTypesExamples.v",
    "ProtocolIRExpressions.v",
    "ProtocolIRExpressionsExamples.v",
    "ProtocolIRActions.v",
    "ProtocolIRActionsExamples.v",
    "ProtocolIRInterpreter.v",
    "ProtocolIRInterpreterExamples.v",
    "ProtocolIRRunner.v",
    "ProtocolIRRunnerExamples.v",
    "ProtocolIRExport.v",
    "ProtocolIRExportExamples.v",
)


def counter_descriptor(theories: Path) -> rocq_codegen.ProtocolExportDescriptor:
    return rocq_codegen.ProtocolExportDescriptor(
        protocol_id="counter",
        schema_version=1,
        ir_version=1,
        logical_root="EchoVerif",
        imports=("ProtocolIRExport", "ProtocolIRExportExamples"),
        export=rocq_codegen.RocqStringExport(
            expression="counter_program_sexpr",
            compiled_module=theories / "ProtocolIRExportExamples.vo",
            sources=tuple(theories / name for name in GENERIC_MODULES),
        ),
    )


def echo_descriptor(theories: Path) -> rocq_codegen.ProtocolExportDescriptor:
    return rocq_codegen.ProtocolExportDescriptor(
        protocol_id="echo",
        schema_version=1,
        ir_version=1,
        logical_root="EchoVerif",
        imports=("ProtocolIRExport", "EchoIRExport"),
        export=rocq_codegen.RocqStringExport(
            expression="echo_ir_program_sexpr",
            compiled_module=theories / "EchoIRExport.vo",
            sources=tuple(theories / name for name in GENERIC_MODULES)
            + tuple(
                theories / name
                for name in (
                    "EchoIRSignature.v",
                    "EchoIRProgram.v",
                    "EchoIRExecutable.v",
                    "EchoIRConformance.v",
                    "EchoIRExport.v",
                )
            ),
        ),
    )
