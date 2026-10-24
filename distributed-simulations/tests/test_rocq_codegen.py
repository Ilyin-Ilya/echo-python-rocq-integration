import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from tools.rocq_codegen import (
    GenerationError,
    ProtocolExportDescriptor,
    RocqStringExport,
    find_coqtop,
    parse_protocol_envelope,
    parse_sexpr,
    write_or_check,
)


class RocqCodegenTests(unittest.TestCase):
    def test_rocq_repl_is_used_when_legacy_coqtop_is_absent(self):
        with tempfile.TemporaryDirectory() as directory:
            rocq = Path(directory) / "rocq"
            rocq.write_text("#!/bin/sh\n", encoding="utf-8")
            rocq.chmod(0o755)
            with mock.patch.dict(os.environ, {"COQBIN": directory}), mock.patch(
                "tools.rocq_codegen.shutil.which", return_value=None
            ):
                self.assertEqual((str(rocq.resolve()), "repl"), find_coqtop(None))

    def protocol_descriptor(self, **overrides):
        values = {
            "protocol_id": "counter",
            "schema_version": 1,
            "ir_version": 1,
            "logical_root": "EchoVerif",
            "imports": ("ProtocolIRExportExamples",),
            "export": RocqStringExport(
                "counter_program_sexpr",
                Path("ProtocolIRExportExamples.vo"),
                (),
            ),
        }
        values.update(overrides)
        return ProtocolExportDescriptor(**values)

    def protocol_source(self, **overrides):
        values = {
            "schema": "1",
            "ir": "1",
            "protocol": "counter",
        }
        values.update(overrides)
        return (
            "(protocol-ir "
            f"(schema-version {values['schema']}) "
            f"(ir-version {values['ir']}) "
            f"(protocol-id {values['protocol']}) "
            "(signature (local-fields)) "
            "(program (rules)))"
        )

    def test_parser_is_protocol_neutral(self):
        self.assertEqual(
            ("protocol", ("rule", "start"), ("rule", "deliver")),
            parse_sexpr("(protocol (rule start) (rule deliver))"),
        )

    def test_parser_rejects_incomplete_or_trailing_data(self):
        for source in ("(protocol", "(protocol) trailing", "protocol"):
            with self.subTest(source=source):
                with self.assertRaises(GenerationError):
                    parse_sexpr(source)

    def test_protocol_envelope_is_validated_before_dispatch(self):
        envelope = parse_protocol_envelope(
            self.protocol_source(), self.protocol_descriptor()
        )
        self.assertEqual("counter", envelope.protocol_id)
        self.assertEqual(1, envelope.schema_version)
        self.assertEqual(1, envelope.ir_version)
        self.assertEqual("signature", envelope.signature[0])
        self.assertEqual("program", envelope.program[0])

    def test_protocol_envelope_rejects_identity_or_version_mismatch(self):
        invalid = (
            self.protocol_source(schema="2"),
            self.protocol_source(ir="2"),
            self.protocol_source(protocol="other"),
        )
        for source in invalid:
            with self.subTest(source=source):
                with self.assertRaises(GenerationError):
                    parse_protocol_envelope(source, self.protocol_descriptor())

    def test_protocol_envelope_rejects_noncanonical_shape(self):
        invalid = (
            "(protocol-ir (ir-version 1) (schema-version 1) "
            "(protocol-id counter) (signature) (program))",
            self.protocol_source()[:-1] + " (extra))",
            "(protocol-ir (schema-version one) (ir-version 1) "
            "(protocol-id counter) (signature) (program))",
            "(protocol-ir (schema-version 1) (ir-version 1) "
            "(protocol-id counter) (program) (signature))",
        )
        for source in invalid:
            with self.subTest(source=source):
                with self.assertRaises(GenerationError):
                    parse_protocol_envelope(source, self.protocol_descriptor())

    def test_protocol_descriptor_rejects_unsafe_protocol_atom(self):
        with self.assertRaises(GenerationError):
            parse_protocol_envelope(
                self.protocol_source(),
                self.protocol_descriptor(protocol_id="counter protocol"),
            )

    def test_outputs_are_replaced_atomically(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "artifact.txt"
            self.assertTrue(write_or_check(target, "first\n", check=False))
            target.chmod(0o640)
            self.assertTrue(write_or_check(target, "second\n", check=False))
            self.assertEqual("second\n", target.read_text(encoding="utf-8"))
            self.assertEqual(0o640, target.stat().st_mode & 0o777)
            self.assertEqual([], list(target.parent.glob(f".{target.name}.*.tmp")))


if __name__ == "__main__":
    unittest.main()
