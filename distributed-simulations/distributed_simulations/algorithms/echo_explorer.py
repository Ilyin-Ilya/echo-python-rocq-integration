"""Bounded exploration of Echo through the generic Rocq-IR interpreter."""

from __future__ import annotations

import argparse
import copy
import json
from collections import deque
from dataclasses import asdict, dataclass
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from ..topology import initiator_id, validate_topology
from .echo_trace import TraceMismatch, _apply_delivery, _expected_start, trace_header


MUTATIONS = (
    "early-root-finish",
    "wrong-parent",
    "drop-pending-removal",
    "duplicate-ack-emission",
    "post-decision-echo",
)


@dataclass(frozen=True)
class ExplorationViolation:
    path: Tuple[int, ...]
    reason: str


@dataclass(frozen=True)
class ExplorationResult:
    explored_states: int
    explored_transitions: int
    completed_states: int
    stuck_states: int
    bounded_states: int
    duplicate_states: int
    max_depth_reached: int
    violation: Optional[ExplorationViolation]

    @property
    def safe(self) -> bool:
        return self.violation is None

    def to_dict(self) -> Dict[str, Any]:
        result = asdict(self)
        result["safe"] = self.safe
        if self.violation is not None:
            result["violation"]["path"] = list(self.violation.path)
        return result


def _state_key(state: Mapping[str, Any]) -> Tuple[Any, ...]:
    """Hash the Rocq-visible state, erasing runtime-only message identifiers."""

    roles = tuple(
        (
            node,
            role["parent"],
            tuple(role["pending"]),
            role["finished"],
        )
        for node, role in sorted(state["state"]["roles"].items())
    )
    messages = tuple(
        sorted(
            (message["kind"], message["sender"], message["receiver"])
            for message in state["store"]
        )
    )
    return state["state"]["started"], roles, messages


def _safety_error(header: Mapping[str, Any], state: Mapping[str, Any]) -> Optional[str]:
    topology = header["topology"]
    root = topology["initiator"]
    roles = state["state"]["roles"]
    if roles[root]["parent"] is not None:
        return "initiator acquired a parent"

    for node, role in roles.items():
        parent = role["parent"]
        if parent is not None and parent not in topology["neighbors"][node]:
            return f"parent edge {parent}->{node} is not in the topology"

    if roles[root]["finished"]:
        for message in state["store"]:
            if message["kind"] == "ECHO" and message["receiver"] == root:
                return "queued ECHO targets the initiator after decision"
        for node in roles:
            seen = set()
            current = node
            while current != root:
                if current in seen:
                    return f"parent cycle reached from {node}"
                seen.add(current)
                parent = roles[current]["parent"]
                if parent is None:
                    return f"node {node} has no parent chain to the initiator"
                current = parent
    return None


def _mutate_successor(
    mutation: Optional[str],
    header: Mapping[str, Any],
    before: Mapping[str, Any],
    message: Mapping[str, Any],
    successor: Mapping[str, Any],
) -> Tuple[Mapping[str, Any], bool]:
    """Apply one controlled implementation fault when its trigger is reached."""

    if mutation is None:
        return successor, False
    mutated = copy.deepcopy(successor)
    root = header["topology"]["initiator"]
    receiver = message["receiver"]
    before_role = before["state"]["roles"][receiver]
    after_role = mutated["state"]["roles"][receiver]

    if mutation == "early-root-finish":
        if not mutated["state"]["roles"][root]["finished"]:
            mutated["state"]["roles"][root]["finished"] = True
            return mutated, True
    elif mutation == "wrong-parent":
        if receiver != root and before_role["parent"] is None and after_role["parent"] is not None:
            candidates = [node for node in sorted(mutated["state"]["roles"]) if node != after_role["parent"]]
            after_role["parent"] = candidates[0]
            return mutated, True
    elif mutation == "drop-pending-removal":
        if message["kind"] == "ACK" and before_role["pending"] != after_role["pending"]:
            after_role["pending"] = list(before_role["pending"])
            return mutated, True
    elif mutation == "duplicate-ack-emission":
        emitted = [
            queued for queued in mutated["store"]
            if queued["message_id"] >= before["next_message_id"]
            and queued["kind"] == "ACK"
        ]
        if emitted:
            duplicate = dict(emitted[0])
            duplicate["message_id"] = mutated["next_message_id"]
            mutated["next_message_id"] += 1
            mutated["store"].append(duplicate)
            return mutated, True
    elif mutation == "post-decision-echo":
        root_before = before["state"]["roles"][root]["finished"]
        root_after = mutated["state"]["roles"][root]["finished"]
        if not root_before and root_after:
            sender = header["topology"]["neighbors"][root][0]
            mutated["store"].append(
                {
                    "message_id": mutated["next_message_id"],
                    "kind": "ECHO",
                    "sender": sender,
                    "receiver": root,
                    "payload": {},
                }
            )
            mutated["next_message_id"] += 1
            return mutated, True
    return successor, False


def explore_echo(
    topology: Mapping[str, Mapping[str, Any]],
    *,
    max_depth: int = 100,
    max_states: int = 100_000,
    mutation: Optional[str] = None,
) -> ExplorationResult:
    """Explore every delivery choice up to the supplied state/depth bounds."""

    if max_depth < 0:
        raise ValueError("max_depth must be non-negative")
    if max_states <= 0:
        raise ValueError("max_states must be positive")
    if mutation is not None and mutation not in MUTATIONS:
        raise ValueError(f"unknown mutation: {mutation}")
    validate_topology(topology)
    root = initiator_id(topology)
    header = trace_header(topology, root, seed=0, max_steps=max_depth)
    initial = _expected_start(header)
    frontier = deque([(initial, tuple())])
    visited = {_state_key(initial)}
    transitions = completed = stuck = bounded = duplicates = 0
    max_reached = 0

    while frontier:
        state, path = frontier.popleft()
        max_reached = max(max_reached, len(path))
        error = _safety_error(header, state)
        if error is not None:
            return ExplorationResult(
                len(visited), transitions, completed, stuck, bounded,
                duplicates, max_reached, ExplorationViolation(path, error)
            )

        all_finished = all(
            role["finished"] for role in state["state"]["roles"].values()
        )
        if not state["store"]:
            if all_finished:
                completed += 1
            else:
                stuck += 1
            continue
        if len(path) >= max_depth:
            bounded += 1
            continue

        for message in state["store"]:
            transitions += 1
            delivery = {"event": "deliver", **message}
            next_path = path + (message["message_id"],)
            try:
                reference = _apply_delivery(header, state, delivery, transitions)
            except (TraceMismatch, ValueError, KeyError) as error:
                return ExplorationResult(
                    len(visited), transitions, completed, stuck, bounded,
                    duplicates, max_reached,
                    ExplorationViolation(next_path, str(error)),
                )
            successor, mutation_applied = _mutate_successor(
                mutation, header, state, message, reference
            )
            if mutation_applied and successor != reference:
                return ExplorationResult(
                    len(visited), transitions, completed, stuck, bounded,
                    duplicates, max_reached,
                    ExplorationViolation(
                        next_path,
                        f"mutation {mutation} differs from generated Echo transition",
                    ),
                )
            key = _state_key(successor)
            if key in visited:
                duplicates += 1
                continue
            if len(visited) >= max_states:
                bounded += 1
                continue
            visited.add(key)
            frontier.append((successor, next_path))

    return ExplorationResult(
        len(visited), transitions, completed, stuck, bounded,
        duplicates, max_reached, None
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Exhaustively explore bounded Echo message schedules."
    )
    parser.add_argument("topology", type=argparse.FileType("r"))
    parser.add_argument("--max-depth", type=int, default=100)
    parser.add_argument("--max-states", type=int, default=100_000)
    parser.add_argument("--mutation", choices=MUTATIONS)
    args = parser.parse_args()
    topology = json.load(args.topology)
    result = explore_echo(
        topology,
        max_depth=args.max_depth,
        max_states=args.max_states,
        mutation=args.mutation,
    )
    print(json.dumps(result.to_dict(), indent=2, sort_keys=True))
    if not result.safe:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
