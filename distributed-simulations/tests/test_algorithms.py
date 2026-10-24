import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import distributed_simulations.algorithms.echo as echo_module
from distributed_simulations.algorithms import (
    run_bracha_toueg,
    run_dijkstra_scholten,
    run_echo,
    run_lai_yang,
)
from distributed_simulations.algorithms.echo_trace import (
    TraceMismatch,
    check_trace_file,
)
from distributed_simulations.algorithms.echo_explorer import MUTATIONS, explore_echo
from distributed_simulations.algorithms.echo_topologies import (
    binary_tree_topology,
    dense_topology,
    line_topology,
    ring_topology,
)
from distributed_simulations.algorithms.echo_evaluation import run_evaluation
from distributed_simulations.runtime import RunOutcome
from distributed_simulations.topology import load_topology, validate_topology


ROOT = Path(__file__).resolve().parent.parent


class AlgorithmTests(unittest.TestCase):
    def topology(self, name):
        return load_topology(ROOT / "examples" / f"{name}.json")

    def test_echo_completes_on_ring_for_multiple_schedules(self):
        topology = self.topology("echo")
        for seed in range(20):
            with self.subTest(seed=seed):
                result = run_echo(topology, seed=seed)
                self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
                self.assertTrue(result.verified)
                self.assertEqual(3, len(result.details["parents"]))
                self.assertTrue(result.details["canonical_runner_proof_covered"])
                self.assertEqual(
                    "runtime-check-and-canonical-runner-proof",
                    result.details["verification_scope"],
                )

    def test_generic_echo_runner_preserves_message_ids(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "generated-echo.jsonl"
            result = run_echo(
                ring_topology(5),
                seed=7,
                log_path=path,
            )
            records = [json.loads(line) for line in path.read_text().splitlines()]
            enqueued_ids = [
                record["message_id"]
                for record in records
                if record.get("event") == "enqueue"
            ]
            checked = check_trace_file(path)
        self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
        self.assertEqual(list(range(1, len(enqueued_ids) + 1)), enqueued_ids)
        self.assertEqual(result.run.steps, checked.transitions)

    def test_echo_production_path_calls_generated_runner_once(self):
        with patch.object(
            echo_module.generated_echo_executable,
            "run_callback",
            wraps=echo_module.generated_echo_executable.run_callback,
        ) as generated_run:
            result = run_echo(ring_topology(5), seed=7)

        self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
        generated_run.assert_called_once()

    def test_echo_reports_step_bound(self):
        result = run_echo(self.topology("echo"), seed=0, max_steps=1)
        self.assertEqual(RunOutcome.BOUNDED, result.run.outcome)
        self.assertFalse(result.verified)

    def test_echo_validates_direct_topology_input(self):
        with self.assertRaisesRegex(ValueError, "not symmetric"):
            run_echo(
                {
                    "A": {"role": "initiator", "neighbors": ["B"]},
                    "B": {"role": "participant", "neighbors": []},
                }
            )

    def test_echo_completes_singleton_topology(self):
        result = run_echo(
            {"A": {"role": "initiator", "neighbors": []}},
            seed=0,
        )
        self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
        self.assertTrue(result.verified)
        self.assertEqual({}, result.details["parents"])
        self.assertTrue(result.details["canonical_runner_proof_covered"])
        self.assertEqual(
            "runtime-check-and-canonical-runner-proof",
            result.details["verification_scope"],
        )

    def test_echo_versioned_trace_passes_generic_ir_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "echo.jsonl"
            result = run_echo(self.topology("echo"), seed=7, log_path=path)
            checked = check_trace_file(path)
        self.assertEqual(result.run.steps, checked.transitions)

    def test_echo_trace_checker_accepts_partial_and_singleton_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            partial = Path(directory) / "partial.jsonl"
            singleton = Path(directory) / "singleton.jsonl"
            partial_result = run_echo(
                self.topology("echo"), seed=3, max_steps=1, log_path=partial
            )
            singleton_result = run_echo(
                {"A": {"role": "initiator", "neighbors": []}},
                seed=3,
                log_path=singleton,
            )
            partial_checked = check_trace_file(partial)
            singleton_checked = check_trace_file(singleton)
        self.assertEqual(partial_result.run.steps, partial_checked.transitions)
        self.assertEqual(
            singleton_result.run.steps, singleton_checked.transitions
        )

    def test_echo_trace_checker_reports_first_bad_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "echo.jsonl"
            run_echo(self.topology("echo"), seed=7, log_path=path)
            records = [json.loads(line) for line in path.read_text().splitlines()]
            snapshot = next(
                record
                for record in records
                if record.get("event") == "snapshot"
                and record.get("point") == "after_delivery"
            )
            snapshot["next_message_id"] += 1
            path.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(TraceMismatch, "snapshot differs"):
                check_trace_file(path)

    def test_echo_trace_checker_rejects_wrong_rocq_artifact_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "echo.jsonl"
            run_echo(self.topology("echo"), seed=7, log_path=path)
            records = [json.loads(line) for line in path.read_text().splitlines()]
            records[0]["rocq_program_sha256"] = "0" * 64
            path.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(TraceMismatch, "program digest mismatch"):
                check_trace_file(path)

    def test_echo_trace_checker_rejects_wrong_ir_version(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "echo.jsonl"
            run_echo(self.topology("echo"), seed=7, log_path=path)
            records = [json.loads(line) for line in path.read_text().splitlines()]
            records[0]["rocq_ir_version"] += 1
            path.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(TraceMismatch, "language version mismatch"):
                check_trace_file(path)

    def test_echo_explorer_checks_all_ring_schedules(self):
        result = explore_echo(self.topology("echo"), max_depth=20)
        self.assertTrue(result.safe)
        self.assertGreater(result.completed_states, 0)
        self.assertEqual(0, result.stuck_states)
        self.assertGreater(result.duplicate_states, 0)

    def test_echo_explorer_handles_singleton(self):
        result = explore_echo(
            {"A": {"role": "initiator", "neighbors": []}},
            max_depth=0,
        )
        self.assertTrue(result.safe)
        self.assertEqual(1, result.completed_states)
        self.assertEqual(1, result.explored_states)

    def test_echo_explorer_generated_topology_matrix(self):
        cases = (
            line_topology(5),
            binary_tree_topology(7),
            ring_topology(5),
            dense_topology(4),
        )
        for topology in cases:
            with self.subTest(topology=topology):
                result = explore_echo(
                    topology,
                    max_depth=40,
                    max_states=100_000,
                )
                self.assertTrue(result.safe)
                self.assertGreater(result.completed_states, 0)
                self.assertEqual(0, result.stuck_states)

    def test_echo_explorer_detects_every_controlled_mutation(self):
        topology = ring_topology(4)
        for mutation in MUTATIONS:
            with self.subTest(mutation=mutation):
                result = explore_echo(
                    topology, max_depth=20, max_states=100_000,
                    mutation=mutation,
                )
                self.assertFalse(result.safe)
                self.assertIsNotNone(result.violation)
                self.assertGreater(len(result.violation.path), 0)

    def test_echo_evaluation_detects_all_mutations(self):
        evaluation = run_evaluation()
        self.assertEqual(1.0, evaluation["mutation_detection"]["rate"])
        self.assertTrue(all(result["safe"] for result in evaluation["topologies"]))

    def test_dijkstra_scholten_completes_on_ring(self):
        topology = self.topology("dijkstra_scholten")
        for seed in range(20):
            with self.subTest(seed=seed):
                result = run_dijkstra_scholten(topology, seed=seed)
                self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
                self.assertTrue(result.verified)
                self.assertEqual(
                    {"A": 0, "B": 0, "C": 0, "D": 0},
                    result.details["ref_counts"],
                )

    def test_lai_yang_collects_every_snapshot(self):
        result = run_lai_yang(self.topology("lai_yang"), seed=7)
        self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
        self.assertTrue(result.verified)
        self.assertEqual({"A", "B", "C", "D"}, set(result.details["snapshots"]))

    def test_bracha_toueg_detects_configured_cycle(self):
        result = run_bracha_toueg(self.topology("bracha_toueg"), seed=7)
        self.assertEqual(RunOutcome.COMPLETE, result.run.outcome)
        self.assertTrue(result.verified)
        self.assertEqual(
            ["A", "B", "C", "D"], result.details["deadlocked_roles"]
        )

    def test_topology_rejects_asymmetric_edge(self):
        with self.assertRaisesRegex(ValueError, "not symmetric"):
            validate_topology(
                {
                    "A": {"role": "initiator", "neighbors": ["B"]},
                    "B": {"role": "participant", "neighbors": []},
                }
            )

    def test_topology_rejects_malformed_node(self):
        with self.assertRaisesRegex(ValueError, "must be a JSON object"):
            validate_topology({"A": None})

    def test_topology_rejects_request_to_non_neighbor(self):
        with self.assertRaisesRegex(ValueError, "non-neighbor requests"):
            validate_topology(
                {
                    "A": {
                        "role": "initiator",
                        "neighbors": ["B"],
                        "requests": ["C"],
                    },
                    "B": {"role": "participant", "neighbors": ["A", "C"]},
                    "C": {"role": "participant", "neighbors": ["B"]},
                }
            )


if __name__ == "__main__":
    unittest.main()
