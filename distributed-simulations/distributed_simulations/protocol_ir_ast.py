"""Typed abstract syntax for protocol programs exported by Rocq.

The classes in this module describe a protocol program.  They do not decode
exports, interpret expressions, execute actions, or contain runtime state
transition logic.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple

from .protocol_values import FieldDeclaration, FieldStore, IRType


SUPPORTED_EXPRESSION_CONSTRUCTORS = (
    "literal",
    "config",
    "global",
    "local",
    "option-some",
    "option-get",
    "message-id",
    "message-sender",
    "message-receiver",
    "message-kind-is",
    "payload",
    "start-certificate",
    "delivery-certificate",
    "is-start",
    "is-delivery",
    "message-store-empty",
    "message-store-length",
    "next-message-id",
    "neighbors",
    "not",
    "and",
    "or",
    "equal",
    "option-is-some",
    "list-is-empty",
    "list-contains",
    "list-remove",
    "list-append",
    "list-permutation",
    "list-length",
    "nat-add",
    "nat-succ",
    "all-nodes-local-equal",
)

SUPPORTED_ACTION_CONSTRUCTORS = (
    "skip",
    "set-global",
    "set-local",
    "remove-selected-message",
    "emit",
    "emit-many",
    "sequence",
)

SUPPORTED_EVENT_PATTERNS = ("start", "deliver")


@dataclass(frozen=True)
class IRCapabilityManifest:
    schema_version: int
    ir_version: int
    types: Tuple[str, ...]
    expressions: Tuple[str, ...]
    actions: Tuple[str, ...]
    event_patterns: Tuple[str, ...]


@dataclass(frozen=True)
class ProtocolSignature:
    local_fields: Tuple[FieldDeclaration, ...]
    global_fields: Tuple[FieldDeclaration, ...]
    config_fields: Tuple[FieldDeclaration, ...]
    message_kinds: Tuple[str, ...]
    payload_fields: Tuple[FieldDeclaration, ...]
    start_certificate_fields: Tuple[FieldDeclaration, ...]
    delivery_certificate_fields: Tuple[FieldDeclaration, ...]
    rule_ids: Tuple[str, ...]


@dataclass(frozen=True)
class Expression:
    operator: str
    arguments: Tuple[Any, ...]
    result_type: IRType


@dataclass(frozen=True)
class Action:
    operator: str
    arguments: Tuple[Any, ...] = ()


@dataclass(frozen=True)
class EventPattern:
    kind: str
    message_kind: Optional[str] = None


@dataclass(frozen=True)
class Rule:
    identifier: str
    pattern: EventPattern
    guards: Tuple[Expression, ...]
    action: Action


@dataclass(frozen=True)
class ProtocolProgram:
    protocol_id: str
    schema_version: int
    ir_version: int
    signature: ProtocolSignature
    initial_local: FieldStore
    initial_global: FieldStore
    initial_next_message_id: int
    rules: Tuple[Rule, ...]
    complete: Expression
    stuck: Expression


@dataclass(frozen=True)
class RuntimeContract:
    """Protocol metadata exposed to a human-written runtime adapter."""

    protocol_id: str
    schema_version: int
    ir_version: int
    config_fields: Tuple[FieldDeclaration, ...]
    start_certificate_fields: Tuple[FieldDeclaration, ...]
    delivery_certificate_fields: Tuple[FieldDeclaration, ...]
    message_kinds: Tuple[str, ...]
    payload_fields: Tuple[FieldDeclaration, ...]
    diagnostic_rule_ids: Tuple[str, ...]


__all__ = [
    "Action",
    "EventPattern",
    "Expression",
    "IRCapabilityManifest",
    "ProtocolProgram",
    "ProtocolSignature",
    "Rule",
    "RuntimeContract",
    "SUPPORTED_ACTION_CONSTRUCTORS",
    "SUPPORTED_EVENT_PATTERNS",
    "SUPPORTED_EXPRESSION_CONSTRUCTORS",
]
