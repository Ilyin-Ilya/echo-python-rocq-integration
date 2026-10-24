import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from distributed_simulations.migration import generated_echo_oracles
from distributed_simulations.migration import generated_echo_program


ROOT = Path(__file__).resolve().parent.parent
GENERATOR = ROOT / "tools" / "generate_echo_oracles_from_rocq.py"
PROGRAM_GENERATOR = ROOT / "tools" / "generate_echo_migration_data_from_rocq.py"


class EchoOracleGenerationTests(unittest.TestCase):
    """Checks that require the optional migration Rocq project to be built."""

    def test_generated_oracles_are_current(self):
        result = subprocess.run(
            [sys.executable, str(GENERATOR), "--check"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(0, result.returncode, result.stderr)

    def test_serialized_generic_program_is_current(self):
        result = subprocess.run(
            [sys.executable, str(PROGRAM_GENERATOR), "--check"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(0, result.returncode, result.stderr)

    def test_serialized_program_check_rejects_manual_edits(self):
        with tempfile.TemporaryDirectory() as directory:
            temporary = Path(directory) / "generated_echo_program.py"
            shutil.copyfile(Path(generated_echo_program.__file__), temporary)
            temporary.write_text(
                temporary.read_text(encoding="utf-8") + "\n# manual edit\n",
                encoding="utf-8",
            )
            result = subprocess.run(
                [
                    sys.executable,
                    str(PROGRAM_GENERATOR),
                    "--output",
                    str(temporary),
                    "--check",
                ],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
            )
            self.assertEqual(1, result.returncode)
            self.assertIn("stale", result.stderr)

    def test_check_rejects_manual_oracle_edits(self):
        sources = {
            "program": ROOT / "bridge" / "rocq_echo_program.sexp",
            "vectors": ROOT / "bridge" / "rocq_echo_vectors.sexp",
            "runs": ROOT / "bridge" / "rocq_echo_run_vectors.sexp",
            "python": Path(generated_echo_oracles.__file__),
        }
        for changed in sources:
            with (
                self.subTest(changed=changed),
                tempfile.TemporaryDirectory() as directory,
            ):
                temporary = Path(directory)
                copies = {name: temporary / path.name for name, path in sources.items()}
                for name, source in sources.items():
                    shutil.copyfile(source, copies[name])
                copies[changed].write_text(
                    copies[changed].read_text(encoding="utf-8") + "\n(manual-edit)\n",
                    encoding="utf-8",
                )
                result = subprocess.run(
                    [
                        sys.executable,
                        str(GENERATOR),
                        "--program-output",
                        str(copies["program"]),
                        "--vectors-output",
                        str(copies["vectors"]),
                        "--run-vectors-output",
                        str(copies["runs"]),
                        "--python-output",
                        str(copies["python"]),
                        "--check",
                    ],
                    cwd=ROOT,
                    check=False,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(1, result.returncode)
                self.assertIn("stale", result.stderr)


if __name__ == "__main__":
    unittest.main()
