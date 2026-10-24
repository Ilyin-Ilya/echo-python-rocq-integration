import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
LEGACY_BRIDGE_PATHS = (
    ROOT / "distributed_simulations" / "algorithms" / "echo_core.py",
    ROOT / "distributed_simulations" / "algorithms" / "echo_generated_adapter.py",
    ROOT / "distributed_simulations" / "rocq_bridge.py",
    ROOT / "tools" / "generate_python_echo_bridge.py",
    ROOT / "bridge" / "python_echo_ir.json",
    ROOT / "tests" / "test_rocq_bridge.py",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "GeneratedPythonEcho.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoGeneratedBridge.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "EchoExecutable.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoStep.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoReplay.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoDecision.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoSnapshot.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoForwardSimulation.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoCorrectness.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoExtraction.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "EchoTransitionCompatibility.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonRefinement.v",
    ROOT.parent / "echo-algorithm-coq" / "theories" / "PythonEchoRefinement.v",
)
HISTORICAL_ROCQ_PROOF_PATHS = tuple(
    ROOT.parent / "echo-algorithm-coq" / "theories" / name
    for name in (
        "EchoExecutableTypes.v",
        "EchoExecutableAbstraction.v",
        "EchoExecutableRefinement.v",
        "EchoExecutableCorrect.v",
        "EchoExecutableSpanningTree.v",
    )
)
RETIRED_PYTHON_IDENTIFIER = re.compile(
    r"\b(?:py_[A-Za-z0-9_]*|PyECHO|PyACK|mkPy[A-Za-z0-9_]*|"
    r"python_[A-Za-z0-9_]*|PythonEchoStep|echo_initial)\b"
)


class MigrationBoundaryTests(unittest.TestCase):
    def test_retired_bridge_files_and_identifiers_remain_absent(self):
        remaining = [str(path) for path in LEGACY_BRIDGE_PATHS if path.exists()]
        self.assertEqual([], remaining)
        legacy_identifiers = [
            f"{path}:{match.group(0)}"
            for path in HISTORICAL_ROCQ_PROOF_PATHS
            for match in RETIRED_PYTHON_IDENTIFIER.finditer(
                path.read_text(encoding="utf-8")
            )
        ]
        self.assertEqual([], legacy_identifiers)

    def test_production_python_has_no_migration_imports(self):
        production_files = (
            *(ROOT / "distributed_simulations" / "algorithms").glob("*.py"),
            ROOT / "distributed_simulations" / "protocol_values.py",
            ROOT / "distributed_simulations" / "protocol_compiled_runtime.py",
        )
        forbidden = (
            "distributed_simulations.migration",
            "generated_echo_program",
            "generated_echo_oracles",
            "echo_ir_adapter",
        )
        violations = []
        for path in production_files:
            source = path.read_text(encoding="utf-8")
            for marker in forbidden:
                if marker in source:
                    violations.append(f"{path.name}:{marker}")
        self.assertEqual([], violations)

    def test_production_generator_owns_only_the_executable(self):
        generator = ROOT / "tools" / "generate_echo_program_from_rocq.py"
        source = generator.read_text(encoding="utf-8")
        self.assertIn("generated_echo_executable.py", source)
        self.assertNotIn("generated_echo_program.py", source)
        self.assertNotIn("render_protocol_data_module", source)
        self.assertNotIn("ROCQ_CONFORMANCE_TREE", source)
        self.assertEqual(1, source.count("rocq_codegen.write_or_check("))


if __name__ == "__main__":
    unittest.main()
