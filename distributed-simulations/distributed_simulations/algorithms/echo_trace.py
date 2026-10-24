"""Versioned Echo traces replayed by the Rocq-generated Python executable."""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence

from ..protocol_values import StepSuccess
from ..runtime import RoleId
from ..topology import validate_topology
from .echo_codec import (
    config_from_trace,
    snapshot_from_protocol_state,
    state_from_trace,
)
from . import generated_echo_executable
from .generated_echo_executable import (
    IR_VERSION,
    ROCQ_PROGRAM_DIGEST,
    SCHEMA_VERSION,
)


TRACE_SCHEMA = "distributed-simulations.echo/v3"


def _code_revision() -> str:
    try:
        return "package:" + importlib.metadata.version("distributed-simulations")
    except importlib.metadata.PackageNotFoundError:
        return "source-tree"


def canonical_topology(
    topology: Mapping[str, Mapping[str, Any]], initiator: RoleId
) -> Dict[str, Any]:
    return {
        "initiator": str(initiator),
        "neighbors": {
            node: list(config.get("neighbors", []))
            for node, config in sorted(topology.items())
        },
    }


def topology_digest(topology: Mapping[str, Any]) -> str:
    encoded = json.dumps(
        topology, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def trace_header(
    topology: Mapping[str, Mapping[str, Any]],
    initiator: RoleId,
    seed: int,
    max_steps: int,
) -> Dict[str, Any]:
    canonical = canonical_topology(topology, initiator)
    return {
        "event": "trace_header",
        "schema": TRACE_SCHEMA,
        "algorithm": "echo",
        "topology": canonical,
        "topology_sha256": topology_digest(canonical),
        "seed": seed,
        "max_steps": max_steps,
        "python_version": platform.python_version(),
        "code_revision": _code_revision(),
        "rocq_program_sha256": ROCQ_PROGRAM_DIGEST,
        "rocq_ir_schema_version": SCHEMA_VERSION,
        "rocq_ir_version": IR_VERSION,
    }


@dataclass(frozen=True)
class TraceCheckResult:
    transitions: int
    final_step: int


class TraceMismatch(ValueError):
    def __init__(self, event_index: int, message: str):
        super().__init__(f"event {event_index}: {message}")
        self.event_index = event_index


def _without_event_fields(record: Mapping[str, Any]) -> Dict[str, Any]:
    return {
        "state": record["state"],
        "store": record["store"],
        "next_message_id": record["next_message_id"],
    }


def _expected_start(header: Mapping[str, Any]) -> Dict[str, Any]:
    config = config_from_trace(header)
    result = generated_echo_executable.step(
        config,
        generated_echo_executable.initialize_protocol(),
        generated_echo_executable.start_event(),
    )
    if not isinstance(result, StepSuccess):
        raise TraceMismatch(0, "generated Echo executable rejected startup")
    return snapshot_from_protocol_state(header, result.state)


def _apply_delivery(
    header: Mapping[str, Any],
    before: Mapping[str, Any],
    delivery: Mapping[str, Any],
    event_index: int,
) -> Dict[str, Any]:
    store = list(before["store"])
    selected = [
        message
        for message in store
        if message["message_id"] == delivery.get("message_id")
    ]
    if len(selected) != 1:
        raise TraceMismatch(event_index, "delivered message id is not uniquely queued")
    message = selected[0]
    for field in ("kind", "sender", "receiver", "payload"):
        if message[field] != delivery.get(field):
            raise TraceMismatch(event_index, f"delivered {field} differs from queue")

    config = config_from_trace(header)
    state = state_from_trace(before)
    event = generated_echo_executable.deliver(message["message_id"])
    result = generated_echo_executable.step(config, state, event)
    if not isinstance(result, StepSuccess):
        raise TraceMismatch(
            event_index,
            f"generated Echo executable rejected queued message "
            f"{message['message_id']}",
        )
    return snapshot_from_protocol_state(header, result.state)


def check_trace(events: Sequence[Mapping[str, Any]]) -> TraceCheckResult:
    if not events:
        raise TraceMismatch(0, "trace is empty")
    header = events[0]
    if header.get("event") != "trace_header":
        raise TraceMismatch(0, "first record is not a trace header")
    if header.get("schema") != TRACE_SCHEMA:
        raise TraceMismatch(0, "unsupported trace schema")
    if header.get("algorithm") != "echo":
        raise TraceMismatch(0, "trace algorithm is not echo")
    if header.get("rocq_program_sha256") != ROCQ_PROGRAM_DIGEST:
        raise TraceMismatch(0, "Rocq program digest mismatch")
    if header.get("rocq_ir_schema_version") != SCHEMA_VERSION:
        raise TraceMismatch(0, "Rocq IR schema version mismatch")
    if header.get("rocq_ir_version") != IR_VERSION:
        raise TraceMismatch(0, "Rocq IR language version mismatch")
    topology = header.get("topology")
    if not isinstance(topology, Mapping):
        raise TraceMismatch(0, "header topology is not an object")
    if topology_digest(topology) != header.get("topology_sha256"):
        raise TraceMismatch(0, "topology digest mismatch")
    root = topology.get("initiator")
    neighbor_map = topology.get("neighbors")
    if not isinstance(root, str) or not isinstance(neighbor_map, Mapping):
        raise TraceMismatch(0, "header topology has invalid shape")
    validation_topology = {
        node: {
            "role": "initiator" if node == root else "participant",
            "neighbors": neighbors,
        }
        for node, neighbors in neighbor_map.items()
    }
    try:
        validate_topology(validation_topology)
    except ValueError as error:
        raise TraceMismatch(0, f"invalid topology: {error}") from error
    if root not in neighbor_map:
        raise TraceMismatch(0, "initiator is not a topology node")

    snapshots = [
        (index, event)
        for index, event in enumerate(events)
        if event.get("event") == "snapshot"
    ]
    if not snapshots:
        raise TraceMismatch(len(events), "trace contains no snapshots")
    first_index, first = snapshots[0]
    if first.get("point") != "after_start" or first.get("step") != 0:
        raise TraceMismatch(first_index, "first snapshot is not after startup")
    before = _without_event_fields(first)
    expected_start = _expected_start(header)
    if before != expected_start:
        raise TraceMismatch(first_index, "startup snapshot does not match topology")

    transitions = 0
    cursor = first_index + 1
    while cursor < len(events):
        record = events[cursor]
        if record.get("event") != "deliver":
            cursor += 1
            continue
        delivery_index = cursor
        expected = _apply_delivery(header, before, record, delivery_index)
        cursor += 1
        while cursor < len(events) and events[cursor].get("event") != "snapshot":
            cursor += 1
        if cursor == len(events):
            raise TraceMismatch(delivery_index, "delivery has no following snapshot")
        after = events[cursor]
        transitions += 1
        if after.get("step") != transitions or after.get("point") != "after_delivery":
            raise TraceMismatch(cursor, "delivery snapshot has wrong step or point")
        actual = _without_event_fields(after)
        if actual != expected:
            raise TraceMismatch(cursor, "snapshot differs from generated IR transition")
        before = actual
        cursor += 1

    return TraceCheckResult(transitions=transitions, final_step=transitions)


def check_trace_file(path: Path) -> TraceCheckResult:
    events: List[Mapping[str, Any]] = []
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if line.strip():
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError as error:
                    raise TraceMismatch(line_number - 1, "invalid JSON") from error
    return check_trace(events)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Replay a versioned Python Echo JSONL trace with generated Rocq IR."
    )
    parser.add_argument("trace", type=Path)
    args = parser.parse_args()
    try:
        result = check_trace_file(args.trace)
    except TraceMismatch as error:
        parser.exit(1, f"trace mismatch: {error}\n")
    print(
        json.dumps(
            {
                "valid": True,
                "schema": TRACE_SCHEMA,
                "transitions": result.transitions,
                "final_step": result.final_step,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
