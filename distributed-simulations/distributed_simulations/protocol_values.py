"""Immutable protocol values shared by generated and interpreted runtimes.

This module contains no IR syntax tree, expression dispatcher, rule selection,
or protocol-specific behavior.  Both the compiled runtime and the reference
interpreter use these values at their boundary.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping, Optional, Sequence, Tuple


Node = Any
FieldStore = Tuple[Tuple[str, "IRValue"], ...]


class ProtocolIRValidationError(ValueError):
    """A protocol definition or runtime value violates the IR contract."""


class IRType(str, Enum):
    BOOL = "bool"
    NAT = "nat"
    NODE = "node"
    OPTION_NODE = "option-node"
    LIST_NODE = "list-node"
    MESSAGE_REF = "message-ref"


@dataclass(frozen=True)
class IRValue:
    kind: IRType
    value: Any


@dataclass(frozen=True)
class FieldDeclaration:
    name: str
    kind: IRType


@dataclass(frozen=True)
class ProtocolConfig:
    nodes: Tuple[Node, ...]
    neighbors: Tuple[Tuple[Node, Tuple[Node, ...]], ...]
    fields: FieldStore

    def neighbors_of(self, node: Node) -> Tuple[Node, ...]:
        for candidate, neighbors in self.neighbors:
            if candidate == node:
                return neighbors
        return ()


@dataclass(frozen=True)
class Message:
    identifier: int
    kind: str
    sender: Node
    receiver: Node
    payload: FieldStore = ()


@dataclass(frozen=True)
class ProtocolState:
    """Finite representation of the formal model's total process map."""

    default_local: FieldStore
    local_overrides: Tuple[Tuple[Node, FieldStore], ...]
    messages: Tuple[Message, ...]
    globals: FieldStore
    next_message_id: int

    def local_fields(self, node: Node) -> FieldStore:
        for candidate, fields in self.local_overrides:
            if candidate == node:
                return fields
        return self.default_local


@dataclass(frozen=True)
class StartEvent:
    certificates: FieldStore


@dataclass(frozen=True)
class DeliveryEvent:
    message_id: int
    certificates: FieldStore


ExternalEvent = Any


class StepError(str, Enum):
    UNQUEUED_MESSAGE = "unqueued-message"
    NO_ENABLED_RULE = "no-enabled-rule"
    AMBIGUOUS_ENABLED_RULES = "ambiguous-enabled-rules"
    MALFORMED_GUARD = "malformed-guard"
    MALFORMED_ACTION = "malformed-action"


@dataclass(frozen=True)
class StepSuccess:
    rule_id: str
    state: ProtocolState


@dataclass(frozen=True)
class StepFailure:
    error: StepError


StepResult = Any


class RunStatus(str, Enum):
    COMPLETE = "complete"
    STUCK = "stuck"
    SCHEDULE_EXHAUSTED = "schedule-exhausted"
    BOUNDED = "bounded"
    INVALID = "invalid"


@dataclass(frozen=True)
class RunOutcome:
    status: RunStatus
    state: ProtocolState
    steps: int
    event: Optional[ExternalEvent] = None
    error: Optional[str] = None


def runtime_store(
    declarations: Sequence[FieldDeclaration], values: Mapping[str, Any]
) -> FieldStore:
    expected = {declaration.name for declaration in declarations}
    if set(values) != expected:
        raise ProtocolIRValidationError(
            f"runtime fields mismatch: expected {sorted(expected)!r}, "
            f"got {sorted(values)!r}"
        )
    return tuple(
        (declaration.name, runtime_value(declaration.kind, values[declaration.name]))
        for declaration in declarations
    )


def runtime_value(kind: IRType, value: Any) -> IRValue:
    valid = False
    converted = value
    if kind is IRType.BOOL:
        valid = isinstance(value, bool)
    elif kind in (IRType.NAT, IRType.MESSAGE_REF):
        valid = isinstance(value, int) and not isinstance(value, bool) and value >= 0
    elif kind is IRType.NODE:
        valid = value is not None
    elif kind is IRType.OPTION_NODE:
        valid = True
    elif kind is IRType.LIST_NODE:
        valid = isinstance(value, (list, tuple))
        if valid:
            converted = tuple(value)
    if not valid:
        raise ProtocolIRValidationError(f"invalid runtime {kind.value} value {value!r}")
    return IRValue(kind, converted)


def validate_message_id(message_id: Any) -> int:
    if (
        not isinstance(message_id, int)
        or isinstance(message_id, bool)
        or message_id < 0
    ):
        raise ProtocolIRValidationError("message id must be a natural number")
    return message_id


def validate_field_store(
    declarations: Sequence[FieldDeclaration], store: FieldStore
) -> None:
    if not isinstance(store, tuple) or len(store) != len(declarations):
        raise ProtocolIRValidationError("runtime field store has the wrong shape")
    for declaration, entry in zip(declarations, store):
        if (
            not isinstance(entry, tuple)
            or len(entry) != 2
            or entry[0] != declaration.name
            or not isinstance(entry[1], IRValue)
            or entry[1].kind is not declaration.kind
            or runtime_value(declaration.kind, entry[1].value) != entry[1]
        ):
            raise ProtocolIRValidationError(
                f"invalid runtime field {declaration.name!r}"
            )


__all__ = [
    "DeliveryEvent",
    "ExternalEvent",
    "FieldDeclaration",
    "FieldStore",
    "IRType",
    "IRValue",
    "Message",
    "Node",
    "ProtocolConfig",
    "ProtocolIRValidationError",
    "ProtocolState",
    "RunOutcome",
    "RunStatus",
    "StartEvent",
    "StepError",
    "StepFailure",
    "StepResult",
    "StepSuccess",
    "runtime_store",
    "runtime_value",
    "validate_field_store",
    "validate_message_id",
]
