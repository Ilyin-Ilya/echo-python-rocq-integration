"""Optional integrity checks for the retired Echo-specific Rocq oracles."""

import ast
import hashlib
import re
import unittest
from pathlib import Path

from distributed_simulations.migration import generated_echo_oracles
from distributed_simulations.migration.generated_echo_oracles import (
    ROCQ_EVALUATION_VECTORS,
    ROCQ_EVALUATION_VECTORS_SEXPR,
    ROCQ_EVALUATION_VECTORS_SHA256,
    ROCQ_LEGACY_PROGRAM,
    ROCQ_LEGACY_PROGRAM_SEXPR,
    ROCQ_LEGACY_PROGRAM_SHA256,
    ROCQ_RUN_VECTORS,
    ROCQ_RUN_VECTORS_SEXPR,
    ROCQ_RUN_VECTORS_SHA256,
)
from tools.migration.legacy_echo_export import GenerationError, validate_program


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
CANONICAL_ROCQ_PROOF_PATHS = tuple(
    ROOT.parent / "echo-algorithm-coq" / "theories" / name
    for name in (
        "EchoExecutableTypes.v",
        "EchoExecutableAbstraction.v",
        "EchoExecutableRefinement.v",
        "EchoExecutableCorrect.v",
        "EchoExecutableSpanningTree.v",
    )
)
LEGACY_ROCQ_IDENTIFIER = re.compile(
    r"\b(?:py_[A-Za-z0-9_]*|PyECHO|PyACK|mkPy[A-Za-z0-9_]*|"
    r"python_[A-Za-z0-9_]*|PythonEchoStep|echo_initial)\b"
)


class EchoOracleTests(unittest.TestCase):
    def test_generated_module_contains_only_literal_data(self):
        source = Path(generated_echo_oracles.__file__).read_text(encoding="utf-8")
        module = ast.parse(source)
        for statement in module.body:
            if isinstance(statement, ast.Expr):
                self.assertIsInstance(statement.value, ast.Constant)
                continue
            self.assertIsInstance(statement, ast.Assign)
            ast.literal_eval(statement.value)

    def test_generated_module_has_no_transition_api(self):
        for name in (
            "echo_exec",
            "execute_echo",
            "step",
            "start",
            "deliver",
            "run",
            "run_schedule",
        ):
            with self.subTest(name=name):
                self.assertFalse(hasattr(generated_echo_oracles, name))

    def test_oracle_digests_and_vector_counts(self):
        self.assertEqual(9, len(ROCQ_LEGACY_PROGRAM) - 1)
        self.assertEqual(
            hashlib.sha256(ROCQ_LEGACY_PROGRAM_SEXPR.encode("utf-8")).hexdigest(),
            ROCQ_LEGACY_PROGRAM_SHA256,
        )
        self.assertEqual(10, len(ROCQ_EVALUATION_VECTORS) - 2)
        self.assertEqual(
            hashlib.sha256(
                ROCQ_EVALUATION_VECTORS_SEXPR.encode("utf-8")
            ).hexdigest(),
            ROCQ_EVALUATION_VECTORS_SHA256,
        )
        self.assertEqual(7, len(ROCQ_RUN_VECTORS) - 1)
        self.assertEqual(
            hashlib.sha256(ROCQ_RUN_VECTORS_SEXPR.encode("utf-8")).hexdigest(),
            ROCQ_RUN_VECTORS_SHA256,
        )

    def test_generator_rejects_unknown_nested_ir(self):
        start_rule = ROCQ_LEGACY_PROGRAM[1]
        invalid_start = (
            start_rule[0],
            start_rule[1],
            (
                "guards",
                "initial",
                ("permutation", "ordered-nodes", ("unknown-nodes", "initiator")),
            ),
            start_rule[3],
        )
        with self.assertRaisesRegex(GenerationError, "unknown-nodes"):
            validate_program(
                (ROCQ_LEGACY_PROGRAM[0], invalid_start, *ROCQ_LEGACY_PROGRAM[2:])
            )

    def test_generator_rejects_unknown_message_kind(self):
        rule = ROCQ_LEGACY_PROGRAM[2]
        invalid_rule = (
            rule[0],
            rule[1],
            ("guards", ("kind", "unknown-kind"), *rule[2][2:]),
            rule[3],
        )
        with self.assertRaisesRegex(GenerationError, "unknown-kind"):
            validate_program(
                (
                    ROCQ_LEGACY_PROGRAM[0],
                    ROCQ_LEGACY_PROGRAM[1],
                    invalid_rule,
                    *ROCQ_LEGACY_PROGRAM[3:],
                )
            )

    def test_retired_bridge_files_and_identifiers_remain_absent(self):
        remaining = [str(path) for path in LEGACY_BRIDGE_PATHS if path.exists()]
        self.assertEqual([], remaining)
        legacy_identifiers = [
            f"{path}:{match.group(0)}"
            for path in CANONICAL_ROCQ_PROOF_PATHS
            for match in LEGACY_ROCQ_IDENTIFIER.finditer(
                path.read_text(encoding="utf-8")
            )
        ]
        self.assertEqual([], legacy_identifiers)


if __name__ == "__main__":
    unittest.main()
