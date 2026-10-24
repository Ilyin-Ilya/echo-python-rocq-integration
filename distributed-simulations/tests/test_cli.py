import io
import json
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

from distributed_simulations.cli import main


ROOT = Path(__file__).resolve().parent.parent


class CLITests(unittest.TestCase):
    def test_cli_reports_package_version(self):
        with redirect_stdout(io.StringIO()) as output:
            with self.assertRaisesRegex(SystemExit, "0"):
                main(["--version"])
        self.assertEqual("distributed-simulations 0.1.0\n", output.getvalue())

    def test_echo_cli_runs_generated_ir_program(self):
        graph = ROOT / "examples" / "echo.json"
        with redirect_stdout(io.StringIO()) as output:
            exit_code = main(
                ["echo", "--graph", str(graph), "--seed", "7"]
            )
            result = json.loads(output.getvalue())
        self.assertEqual(0, exit_code)
        self.assertEqual("complete", result["outcome"])
        self.assertTrue(result["verified"])

    def test_retired_echo_core_option_is_rejected(self):
        with redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                main(["echo", "--echo-core", "generated"])

    def test_echo_cli_exposes_fifo_scheduler(self):
        graph = ROOT / "examples" / "echo.json"
        with redirect_stdout(io.StringIO()) as output:
            exit_code = main(
                ["echo", "--graph", str(graph), "--scheduler", "fifo"]
            )
            result = json.loads(output.getvalue())
        self.assertEqual(0, exit_code)
        self.assertEqual("complete", result["outcome"])
        self.assertIn("parents", result)

    def test_non_echo_cli_rejects_scheduler_option(self):
        graph = ROOT / "examples" / "dijkstra_scholten.json"
        with redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                main(
                    [
                        "dijkstra-scholten",
                        "--graph",
                        str(graph),
                        "--scheduler",
                        "fifo",
                    ]
                )

    def test_cli_reports_invalid_topology_without_traceback(self):
        missing = ROOT / "examples" / "does-not-exist.json"
        with redirect_stderr(io.StringIO()) as errors:
            with self.assertRaisesRegex(SystemExit, "2"):
                main(["echo", "--graph", str(missing)])
        self.assertIn("error:", errors.getvalue())
        self.assertNotIn("Traceback", errors.getvalue())


if __name__ == "__main__":
    unittest.main()
