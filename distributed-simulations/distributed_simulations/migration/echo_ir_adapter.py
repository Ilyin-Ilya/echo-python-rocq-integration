"""Thin value conversion between Echo snapshots and the generic IR runtime.

This module contains no transition rules.  Echo behavior remains in the Rocq
program data; the adapter only names Echo fields and converts runtime values.
Events contain only startup or a selected queued-message identifier.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional, Sequence, Tuple

from ..protocol_ir_ast import ProtocolProgram
from ..protocol_ir_codec import (
    decode_ir_capability_manifest,
    decode_protocol_program,
)
from ..protocol_ir_interpreter import (
    evaluate_state_predicate,
    make_config,
    make_delivery_event,
    make_start_event,
    runtime_contract,
)
from ..protocol_values import (
    DeliveryEvent,
    FieldDeclaration,
    IRType,
    IRValue,
    Message,
    ProtocolConfig,
    ProtocolIRValidationError,
    ProtocolState,
    StartEvent,
)
from . import generated_echo_program


Node = Any
ECHO = "ECHO"
ACK = "ACK"


@dataclass(frozen=True)
class EchoProcessView:
    parent: Optional[Node] = None
    pending: Tuple[Node, ...] = ()
    finished: bool = False


@dataclass(frozen=True)
class EchoMessageView:
    message_id: int
    kind: str
    sender: Node
    receiver: Node


@dataclass(frozen=True)
class EchoStateView:
    processes: Tuple[Tuple[Node, EchoProcessView], ...]
    messages: Tuple[EchoMessageView, ...]
    started: bool
    next_message_id: int


def load_echo_program() -> ProtocolProgram:
    decode_ir_capability_manifest(
        generated_echo_program.IR_CAPABILITY_TREE,
        expected_schema_version=generated_echo_program.SCHEMA_VERSION,
        expected_ir_version=generated_echo_program.IR_VERSION,
    )
    program = decode_protocol_program(
        generated_echo_program.PROTOCOL_TREE,
        node_decoder=int,
        expected_protocol_id=generated_echo_program.PROTOCOL_ID,
        expected_schema_version=generated_echo_program.SCHEMA_VERSION,
        expected_ir_version=generated_echo_program.IR_VERSION,
    )
    validate_echo_adapter_contract(program)
    return program


def _field_shape(
    fields: Sequence[FieldDeclaration],
) -> Tuple[Tuple[str, IRType], ...]:
    return tuple((field.name, field.kind) for field in fields)


def validate_echo_adapter_contract(program: ProtocolProgram) -> None:
    """Reject formal signature drift that requires a human adapter update."""

    contract = runtime_contract(program)
    actual = (
        _field_shape(contract.config_fields),
        _field_shape(contract.start_certificate_fields),
        _field_shape(contract.delivery_certificate_fields),
        contract.message_kinds,
        _field_shape(contract.payload_fields),
    )
    expected = (
        (("initiator", IRType.NODE),),
        (),
        (),
        ("request", "reply"),
        (),
    )
    if actual != expected:
        raise ProtocolIRValidationError(
            "generated Echo runtime contract changed; update echo_ir_adapter.py"
        )


def echo_config(
    program: ProtocolProgram,
    *,
    initiator: Node,
    nodes: Sequence[Node],
    adjacency: Mapping[Node, Sequence[Node]],
) -> ProtocolConfig:
    return make_config(
        program,
        nodes=nodes,
        neighbors=adjacency,
        fields={"initiator": initiator},
    )


def echo_start_event(program: ProtocolProgram) -> StartEvent:
    return make_start_event(program, {})


def echo_delivery_event(
    program: ProtocolProgram,
    *,
    message_id: int,
) -> DeliveryEvent:
    return make_delivery_event(program, message_id, {})


def echo_event_for_message(
    program: ProtocolProgram,
    message_id: int,
) -> DeliveryEvent:
    return echo_delivery_event(program, message_id=message_id)


def echo_is_complete(
    program: ProtocolProgram, config: ProtocolConfig, state: ProtocolState
) -> bool:
    return evaluate_state_predicate(program.complete, config, state) is True


def echo_message_kind(kind: str) -> str:
    return _checked_kind(
        kind, {"request": ECHO, "reply": ACK}, "formal Echo"
    )


def encode_echo_state(
    program: ProtocolProgram,
    *,
    processes: Mapping[Node, EchoProcessView],
    messages: Sequence[EchoMessageView],
    started: bool,
    next_message_id: int,
) -> ProtocolState:
    message_kinds = {
        "echo": "request",
        ECHO: "request",
        "ack": "reply",
        ACK: "reply",
    }
    return ProtocolState(
        default_local=program.initial_local,
        local_overrides=tuple(
            (
                node,
                (
                    ("parent", IRValue(IRType.OPTION_NODE, process.parent)),
                    ("pending", IRValue(IRType.LIST_NODE, tuple(process.pending))),
                    ("finished", IRValue(IRType.BOOL, process.finished)),
                ),
            )
            for node, process in processes.items()
        ),
        messages=tuple(
            Message(
                message.message_id,
                _checked_kind(message.kind, message_kinds, "runtime Echo"),
                message.sender,
                message.receiver,
                (),
            )
            for message in messages
        ),
        globals=(("started", IRValue(IRType.BOOL, started)),),
        next_message_id=next_message_id,
    )


def decode_echo_state(
    state: ProtocolState, nodes: Sequence[Node]
) -> EchoStateView:
    processes = []
    for node in nodes:
        fields = dict(state.local_fields(node))
        processes.append(
            (
                node,
                EchoProcessView(
                    parent=fields["parent"].value,
                    pending=tuple(fields["pending"].value),
                    finished=fields["finished"].value,
                ),
            )
        )
    messages = tuple(
        EchoMessageView(
            message.identifier,
            _checked_kind(
                message.kind,
                {"request": ECHO, "reply": ACK},
                "formal Echo",
            ),
            message.sender,
            message.receiver,
        )
        for message in state.messages
    )
    return EchoStateView(
        processes=tuple(processes),
        messages=messages,
        started=dict(state.globals)["started"].value,
        next_message_id=state.next_message_id,
    )


def _checked_kind(kind: str, mapping: Mapping[str, str], boundary: str) -> str:
    try:
        return mapping[kind]
    except KeyError as error:
        raise ProtocolIRValidationError(
            f"unknown {boundary} message kind {kind!r}"
        ) from error


__all__ = [
    "EchoMessageView",
    "EchoProcessView",
    "EchoStateView",
    "ACK",
    "ECHO",
    "decode_echo_state",
    "echo_config",
    "echo_delivery_event",
    "echo_event_for_message",
    "echo_is_complete",
    "echo_message_kind",
    "echo_start_event",
    "encode_echo_state",
    "load_echo_program",
    "validate_echo_adapter_contract",
]
