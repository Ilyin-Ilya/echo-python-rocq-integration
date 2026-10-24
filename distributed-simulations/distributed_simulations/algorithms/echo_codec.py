"""Value conversion for the generated Echo executable.

This module contains no transition rules and does not load the serialized IR
tree. It translates public topology/trace values to the stable runtime types
used by ``generated_echo_executable``.
"""

from __future__ import annotations

from typing import Any, Dict, Mapping

from ..protocol_values import (
    IRType,
    IRValue,
    Message,
    ProtocolConfig,
    ProtocolState,
)
from ..runtime import RoleId
from ..topology import Topology
from . import generated_echo_executable


def _formal_message_kind(kind: str) -> str:
    kinds = {
        "echo": "request",
        "ECHO": "request",
        "ack": "reply",
        "ACK": "reply",
        "request": "request",
        "reply": "reply",
    }
    try:
        return kinds[kind]
    except KeyError as error:
        raise ValueError(f"unknown Echo message kind {kind!r}") from error


def _public_message_kind(kind: str) -> str:
    try:
        return {"request": "ECHO", "reply": "ACK"}[kind]
    except KeyError as error:
        raise ValueError(f"unknown formal Echo message kind {kind!r}") from error


def _config(*, initiator: RoleId, nodes, adjacency) -> ProtocolConfig:
    return generated_echo_executable.make_config(
        nodes=tuple(nodes),
        neighbors=adjacency,
        fields={"initiator": initiator},
    )


def config_from_topology(
    topology: Topology,
    initiator: RoleId,
) -> ProtocolConfig:
    """Convert a public topology to the generated protocol configuration."""

    nodes = tuple(RoleId(node) for node in sorted(topology))
    return _config(
        initiator=initiator,
        nodes=nodes,
        adjacency={
            RoleId(node): tuple(
                RoleId(neighbor) for neighbor in config["neighbors"]
            )
            for node, config in topology.items()
        },
    )


def config_from_trace(header: Mapping[str, Any]) -> ProtocolConfig:
    topology = header["topology"]
    nodes = tuple(RoleId(node) for node in sorted(topology["neighbors"]))
    return _config(
        initiator=RoleId(topology["initiator"]),
        nodes=nodes,
        adjacency={
            RoleId(node): tuple(RoleId(neighbor) for neighbor in neighbors)
            for node, neighbors in topology["neighbors"].items()
        },
    )


def state_from_trace(snapshot: Mapping[str, Any]) -> ProtocolState:
    """Rebuild a generated-runtime state from one public trace snapshot."""

    initial = generated_echo_executable.initialize_protocol()
    return ProtocolState(
        default_local=initial.default_local,
        local_overrides=tuple(
            (
                RoleId(node),
                (
                    (
                        "parent",
                        IRValue(
                            IRType.OPTION_NODE,
                            RoleId(role["parent"])
                            if role["parent"] is not None
                            else None,
                        ),
                    ),
                    (
                        "pending",
                        IRValue(
                            IRType.LIST_NODE,
                            tuple(RoleId(item) for item in role["pending"]),
                        ),
                    ),
                    ("finished", IRValue(IRType.BOOL, role["finished"])),
                ),
            )
            for node, role in snapshot["state"]["roles"].items()
        ),
        messages=tuple(
            Message(
                message["message_id"],
                _formal_message_kind(message["kind"]),
                RoleId(message["sender"]),
                RoleId(message["receiver"]),
                (),
            )
            for message in snapshot["store"]
        ),
        globals=(("started", IRValue(IRType.BOOL, snapshot["state"]["started"])),),
        next_message_id=snapshot["next_message_id"],
    )


def snapshot_from_protocol_state(
    header: Mapping[str, Any],
    state: ProtocolState,
) -> Dict[str, Any]:
    root = RoleId(header["topology"]["initiator"])
    nodes = tuple(
        RoleId(node) for node in sorted(header["topology"]["neighbors"])
    )
    roles: Dict[str, Any] = {}
    for node in nodes:
        fields = dict(state.local_fields(node))
        parent = fields["parent"].value
        pending = tuple(fields["pending"].value)
        finished = fields["finished"].value
        if node == root:
            # Preserve the historical public trace view of the initiator.
            finished = dict(state.globals)["started"].value and not pending
        roles[str(node)] = {
            "parent": str(parent) if parent is not None else None,
            "pending": sorted(str(item) for item in pending),
            "finished": finished,
        }
    return {
        "state": {
            "started": dict(state.globals)["started"].value,
            "roles": roles,
        },
        "store": [
            {
                "message_id": message.identifier,
                "kind": _public_message_kind(message.kind),
                "sender": str(message.sender),
                "receiver": str(message.receiver),
                "payload": {},
            }
            for message in state.messages
        ],
        "next_message_id": state.next_message_id,
    }


__all__ = [
    "config_from_topology",
    "config_from_trace",
    "snapshot_from_protocol_state",
    "state_from_trace",
]
