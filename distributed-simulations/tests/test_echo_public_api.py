import unittest
from pathlib import Path

import distributed_simulations
from distributed_simulations.echo import (
    EchoNetwork,
    InvalidRunConfigurationError,
    InvalidTopologyError,
    run_echo,
)
from distributed_simulations.runtime import RunOutcome


ROOT = Path(__file__).resolve().parent.parent


class EchoPublicAPITests(unittest.TestCase):
    def test_edge_list_has_typed_result(self):
        network = EchoNetwork.from_edges(
            (("A", "B"), ("B", "C"), ("C", "A")), initiator="A"
        )

        result = run_echo(network, scheduler="fifo")

        self.assertTrue(result.completed)
        self.assertTrue(result.verified)
        self.assertEqual(RunOutcome.COMPLETE, result.outcome)
        self.assertEqual({"B", "C"}, set(result.parents))
        self.assertTrue(result.verification.canonical_runner_proof_covered)
        self.assertIn("Rocq", result.verification.explanation)
        self.assertEqual("complete", result.to_dict()["outcome"])

    def test_network_and_result_offer_tree_queries(self):
        network = EchoNetwork.from_edges(
            (("A", "B"), ("B", "C")), initiator="A"
        )
        result = run_echo(network, scheduler="fifo")

        self.assertEqual(("A", "B", "C"), network.nodes)
        self.assertEqual((("A", "B"), ("B", "C")), network.edges)
        self.assertEqual(("A", "C"), network.neighbors_of("B"))
        self.assertIsNone(result.parent_of("A"))
        self.assertEqual("A", result.parent_of("B"))
        self.assertEqual(("B",), result.children_of("A"))
        self.assertEqual(("C", "B", "A"), result.path_to_initiator("C"))
        self.assertEqual(
            (("A", "B"), ("B", "C")),
            result.tree_edges,
        )
        self.assertEqual("A", result.to_dict()["initiator"])

        with self.assertRaisesRegex(KeyError, "unknown Echo node"):
            result.path_to_initiator("missing")

    def test_adjacency_and_json_constructors(self):
        adjacency = EchoNetwork.from_adjacency(
            {"A": ("B",), "B": ("A",)}, initiator="A"
        )
        loaded = EchoNetwork.from_json(ROOT / "examples" / "echo.json")

        self.assertTrue(run_echo(adjacency).completed)
        self.assertTrue(run_echo(loaded).completed)

    def test_run_accepts_adjacency_directly_with_initiator(self):
        result = run_echo(
            {"A": ("B",), "B": ("A",)},
            initiator="A",
            scheduler="fifo",
        )

        self.assertTrue(result.completed)
        self.assertEqual({"B": "A"}, dict(result.parents))

    def test_all_public_schedulers_choose_only_queued_messages(self):
        network = EchoNetwork.from_edges(
            (("A", "B"), ("B", "C"), ("C", "D"), ("D", "A")),
            initiator="A",
        )
        for scheduler in ("random", "fifo", "lifo"):
            with self.subTest(scheduler=scheduler):
                self.assertTrue(run_echo(network, scheduler=scheduler).completed)

    def test_custom_scheduler_sees_read_only_message_descriptions(self):
        network = EchoNetwork.from_edges(
            (("A", "B"), ("B", "C"), ("C", "A")), initiator="A"
        )
        choices = []

        def lowest_message_id(messages):
            choices.append(messages)
            return min(message.message_id for message in messages)

        result = run_echo(network, scheduler=lowest_message_id)

        self.assertTrue(result.completed)
        self.assertTrue(choices)
        self.assertEqual("request", choices[0][0].kind)

    def test_custom_scheduler_cannot_select_an_unqueued_message(self):
        network = EchoNetwork.from_edges((("A", "B"),), initiator="A")
        with self.assertRaisesRegex(
            InvalidRunConfigurationError, "unqueued message"
        ):
            run_echo(network, scheduler=lambda _messages: 999)

    def test_trace_capture_and_callback(self):
        network = EchoNetwork.from_edges((("A", "B"),), initiator="A")
        observed = []

        result = run_echo(
            network,
            capture_trace=True,
            on_event=lambda event: observed.append(event["event"]),
        )

        self.assertEqual("trace_header", result.trace[0]["event"])
        self.assertEqual("run_finished", result.trace[-1]["event"])
        self.assertEqual(
            [event["event"] for event in result.trace],
            observed,
        )

    def test_bounded_result_reports_incomplete_paths(self):
        network = EchoNetwork.from_edges(
            (("A", "B"), ("B", "C")), initiator="A"
        )
        result = run_echo(network, max_steps=1)

        self.assertFalse(result.completed)
        self.assertIsNone(result.path_to_initiator("C"))

    def test_public_errors_are_specific(self):
        with self.assertRaisesRegex(InvalidTopologyError, "not symmetric"):
            EchoNetwork.from_adjacency(
                {"A": ("B",), "B": ()}, initiator="A"
            )
        network = EchoNetwork.from_adjacency({"A": ()}, initiator="A")
        with self.assertRaisesRegex(InvalidRunConfigurationError, "scheduler"):
            run_echo(network, scheduler="unknown")  # type: ignore[arg-type]
        with self.assertRaisesRegex(InvalidTopologyError, "exactly two"):
            EchoNetwork.from_edges(("AB",), initiator="A")
        with self.assertRaisesRegex(InvalidTopologyError, "does not match"):
            run_echo(network, initiator="B")

    def test_package_root_exports_friendly_api(self):
        self.assertIs(distributed_simulations.run_echo, run_echo)
        self.assertIs(distributed_simulations.EchoNetwork, EchoNetwork)

    def test_public_facade_contains_no_echo_transition_rules(self):
        source = Path(distributed_simulations.echo.__file__).read_text(
            encoding="utf-8"
        )
        self.assertNotIn("first_request", source)
        self.assertNotIn("repeated_request", source)
        self.assertNotIn("participant_reply", source)
        self.assertNotIn("initiator_reply", source)


if __name__ == "__main__":
    unittest.main()
