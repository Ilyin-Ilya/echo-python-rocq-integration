"""Small runtime library for Python code compiled from the protocol IR.

Generated protocol modules call these immutable state primitives directly.
This module deliberately contains no IR operator dispatcher and no protocol
rules: protocol-specific control flow lives in generated Python source.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from inspect import signature
from typing import Any, Callable, Mapping, Optional, Sequence, Tuple

from .protocol_values import (
    DeliveryEvent,
    ExternalEvent,
    FieldDeclaration,
    FieldStore,
    IRType,
    IRValue,
    Message,
    ProtocolConfig,
    ProtocolIRValidationError,
    ProtocolState,
    RunOutcome,
    RunStatus,
    StartEvent,
    StepFailure,
    runtime_store,
    validate_field_store,
    validate_message_id,
)


COMPILED_RUNTIME_ABI_VERSION = 2
GENERATED_PROTOCOL_API_VERSION = 2
GENERATED_PROTOCOL_PUBLIC_NAMES = (
    "PROTOCOL_ID",
    "SCHEMA_VERSION",
    "IR_VERSION",
    "ROCQ_PROGRAM_DIGEST",
    "RUNTIME_ABI_VERSION",
    "GENERATED_API_VERSION",
    "LOCAL_FIELDS",
    "GLOBAL_FIELDS",
    "CONFIG_FIELDS",
    "PAYLOAD_FIELDS",
    "START_CERTIFICATE_FIELDS",
    "DELIVERY_CERTIFICATE_FIELDS",
    "MESSAGE_KINDS",
    "RULE_IDS",
    "make_config",
    "make_start_event",
    "make_delivery_event",
    "start_event",
    "deliver",
    "initialize_protocol",
    "is_complete",
    "is_stuck",
    "step",
    "run_schedule",
    "run_callback",
)
_GENERATED_PROTOCOL_CALLABLES = (
    "make_config",
    "make_start_event",
    "make_delivery_event",
    "start_event",
    "deliver",
    "initialize_protocol",
    "is_complete",
    "is_stuck",
    "step",
    "run_schedule",
    "run_callback",
)
GENERATED_PROTOCOL_SIGNATURES = (
    ("make_config", "(*, nodes, neighbors, fields)"),
    ("make_start_event", "(fields)"),
    ("make_delivery_event", "(message_id, fields)"),
    ("start_event", "(fields=None)"),
    ("deliver", "(message_id, fields=None)"),
    ("initialize_protocol", "()"),
    ("is_complete", "(config, state)"),
    ("is_stuck", "(config, state)"),
    ("step", "(config, state, external_event)"),
    ("run_schedule", "(config, fuel, schedule, state=None)"),
    (
        "run_callback",
        "(config, *, start_event, scheduler, delivery_event, "
        "max_steps=10000, observer=None)",
    ),
)


class CompiledRuntimeCompatibilityError(RuntimeError):
    """A generated module targets an incompatible compiled-runtime API."""


def require_runtime_abi(expected: int) -> None:
    """Fail clearly when generated code and its support runtime are mismatched."""

    if expected != COMPILED_RUNTIME_ABI_VERSION:
        raise CompiledRuntimeCompatibilityError(
            "generated protocol requires compiled-runtime ABI "
            f"{expected}, but this runtime provides "
            f"{COMPILED_RUNTIME_ABI_VERSION}"
        )


class GeneratedProtocolInterfaceError(RuntimeError):
    """A generated module does not implement the shared public interface."""


def validate_generated_protocol_api(namespace: Mapping[str, Any]) -> None:
    """Validate the stable adapter-facing surface of a generated module."""

    version = namespace.get("GENERATED_API_VERSION")
    if version != GENERATED_PROTOCOL_API_VERSION:
        raise GeneratedProtocolInterfaceError(
            "generated protocol API version mismatch: "
            f"expected {GENERATED_PROTOCOL_API_VERSION}, got {version!r}"
        )
    declared = namespace.get("__all__")
    if declared != GENERATED_PROTOCOL_PUBLIC_NAMES:
        raise GeneratedProtocolInterfaceError(
            "generated protocol __all__ does not match the shared interface"
        )
    missing = [
        name for name in GENERATED_PROTOCOL_PUBLIC_NAMES if name not in namespace
    ]
    noncallable = [
        name
        for name in _GENERATED_PROTOCOL_CALLABLES
        if name in namespace and not callable(namespace[name])
    ]
    if missing or noncallable:
        raise GeneratedProtocolInterfaceError(
            f"invalid generated protocol interface: missing={missing!r}, "
            f"noncallable={noncallable!r}"
        )
    metadata_errors = []
    protocol_id = namespace["PROTOCOL_ID"]
    if not isinstance(protocol_id, str) or not protocol_id:
        metadata_errors.append("PROTOCOL_ID must be a non-empty string")
    for name in ("SCHEMA_VERSION", "IR_VERSION"):
        value = namespace[name]
        if not isinstance(value, int) or isinstance(value, bool) or value < 1:
            metadata_errors.append(f"{name} must be a positive integer")
    digest = namespace["ROCQ_PROGRAM_DIGEST"]
    if (
        not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        metadata_errors.append(
            "ROCQ_PROGRAM_DIGEST must be a lowercase SHA-256 digest"
        )
    field_groups = (
        "LOCAL_FIELDS",
        "GLOBAL_FIELDS",
        "CONFIG_FIELDS",
        "PAYLOAD_FIELDS",
        "START_CERTIFICATE_FIELDS",
        "DELIVERY_CERTIFICATE_FIELDS",
    )
    for name in field_groups:
        declarations = namespace[name]
        valid_declarations = isinstance(declarations, tuple) and all(
            isinstance(declaration, FieldDeclaration)
            and isinstance(declaration.name, str)
            and bool(declaration.name)
            and isinstance(declaration.kind, IRType)
            for declaration in declarations
        )
        unique_names = valid_declarations and len(
            {declaration.name for declaration in declarations}
        ) == len(declarations)
        if not valid_declarations or not unique_names:
            metadata_errors.append(
                f"{name} must contain uniquely named typed field declarations"
            )
    for name in ("MESSAGE_KINDS", "RULE_IDS"):
        identifiers = namespace[name]
        valid_identifiers = isinstance(identifiers, tuple) and all(
            isinstance(identifier, str) and bool(identifier)
            for identifier in identifiers
        )
        unique_identifiers = valid_identifiers and len(set(identifiers)) == len(
            identifiers
        )
        if not valid_identifiers or not unique_identifiers:
            metadata_errors.append(
                f"{name} must contain unique non-empty strings"
            )
    if metadata_errors:
        raise GeneratedProtocolInterfaceError(
            "invalid generated protocol metadata: " + "; ".join(metadata_errors)
        )
    signature_mismatches = []
    for name, expected in GENERATED_PROTOCOL_SIGNATURES:
        actual = str(signature(namespace[name]))
        if actual != expected:
            signature_mismatches.append(
                f"{name}: expected {expected}, got {actual}"
            )
    if signature_mismatches:
        raise GeneratedProtocolInterfaceError(
            "generated protocol signature mismatch: "
            + "; ".join(signature_mismatches)
        )


class CompiledEvaluationFailure(RuntimeError):
    """A generated expression or action is undefined for its runtime input."""


class RuleStatus(str, Enum):
    MISMATCH = "mismatch"
    DISABLED = "disabled"
    MALFORMED = "malformed"
    ENABLED = "enabled"


@dataclass(frozen=True)
class QueryEvent:
    pass


@dataclass(frozen=True)
class ResolvedStart:
    certificates: FieldStore


@dataclass(frozen=True)
class ResolvedDelivery:
    message: Message
    certificates: FieldStore


RuntimeEvent = Any
FieldShape = Tuple[FieldDeclaration, ...]


def resolve_event(
    state: ProtocolState,
    event: ExternalEvent,
    *,
    start_fields: FieldShape,
    delivery_fields: FieldShape,
) -> Optional[RuntimeEvent]:
    if isinstance(event, StartEvent):
        validate_field_store(start_fields, event.certificates)
        return ResolvedStart(event.certificates)
    if isinstance(event, DeliveryEvent):
        validate_message_id(event.message_id)
        validate_field_store(delivery_fields, event.certificates)
        for message in state.messages:
            if message.identifier == event.message_id:
                return ResolvedDelivery(message, event.certificates)
        return None
    raise CompiledEvaluationFailure(f"unknown external event {event!r}")


def pattern_matches(
    event: RuntimeEvent, pattern: str, message_kind: Optional[str] = None
) -> bool:
    if pattern == "start":
        return isinstance(event, ResolvedStart)
    if pattern == "deliver":
        return (
            isinstance(event, ResolvedDelivery)
            and event.message.kind == message_kind
        )
    raise CompiledEvaluationFailure(f"unknown event pattern {pattern!r}")


def message_for(event: RuntimeEvent) -> Message:
    if not isinstance(event, ResolvedDelivery):
        raise CompiledEvaluationFailure("expression requires a delivery event")
    return event.message


def start_certificates(event: RuntimeEvent) -> FieldStore:
    if not isinstance(event, ResolvedStart):
        raise CompiledEvaluationFailure("start certificate read outside startup")
    return event.certificates


def delivery_certificates(event: RuntimeEvent) -> FieldStore:
    if not isinstance(event, ResolvedDelivery):
        raise CompiledEvaluationFailure("delivery certificate read outside delivery")
    return event.certificates


def lookup_value(store: FieldStore, field: str) -> Any:
    for candidate, value in store:
        if candidate == field:
            return value.value
    raise CompiledEvaluationFailure(f"missing field {field!r}")


def local_value(state: ProtocolState, node: Any, field: str) -> Any:
    """Read one local field with a compact generated-code spelling."""

    return lookup_value(state.local_fields(node), field)


def make_config(
    declarations: FieldShape,
    *,
    nodes: Sequence[Any],
    neighbors: Mapping[Any, Sequence[Any]],
    fields: Mapping[str, Any],
) -> ProtocolConfig:
    return ProtocolConfig(
        nodes=tuple(nodes),
        neighbors=tuple(
            (node, tuple(adjacent)) for node, adjacent in neighbors.items()
        ),
        fields=runtime_store(declarations, fields),
    )


def make_start_event(
    declarations: FieldShape, fields: Mapping[str, Any]
) -> StartEvent:
    return StartEvent(runtime_store(declarations, fields))


def make_delivery_event(
    declarations: FieldShape,
    message_id: int,
    fields: Mapping[str, Any],
) -> DeliveryEvent:
    validate_message_id(message_id)
    return DeliveryEvent(message_id, runtime_store(declarations, fields))


def _set_field(store: FieldStore, field: str, value: IRValue) -> FieldStore:
    result = []
    found = False
    for candidate, old_value in store:
        if candidate == field:
            result.append((candidate, value))
            found = True
        else:
            result.append((candidate, old_value))
    if not found:
        raise CompiledEvaluationFailure(f"missing field {field!r}")
    return tuple(result)


def set_global(
    state: ProtocolState, field: str, kind: IRType, raw_value: Any
) -> ProtocolState:
    return replace(
        state,
        globals=_set_field(state.globals, field, IRValue(kind, raw_value)),
    )


def set_local(
    state: ProtocolState,
    node: Any,
    field: str,
    kind: IRType,
    raw_value: Any,
) -> ProtocolState:
    fields = _set_field(
        state.local_fields(node), field, IRValue(kind, raw_value)
    )
    overrides = []
    replaced = False
    for candidate, existing in state.local_overrides:
        if candidate == node:
            overrides.append((candidate, fields))
            replaced = True
        else:
            overrides.append((candidate, existing))
    if not replaced:
        overrides.append((node, fields))
    return replace(state, local_overrides=tuple(overrides))


def remove_first(value: Any, items: Sequence[Any]) -> Tuple[Any, ...]:
    result = []
    removed = False
    for item in items:
        if not removed and item == value:
            removed = True
        else:
            result.append(item)
    return tuple(result)


def is_permutation(left: Sequence[Any], right: Sequence[Any]) -> bool:
    residual = list(right)
    for item in left:
        try:
            index = residual.index(item)
        except ValueError:
            return False
        residual.pop(index)
    return not residual


def option_get(value: Any) -> Any:
    if value is None:
        raise CompiledEvaluationFailure("option-get requires Some(node)")
    return value


def eager_and(left: bool, right: bool) -> bool:
    return left and right


def eager_or(left: bool, right: bool) -> bool:
    return left or right


def all_nodes_local_equal(
    config: ProtocolConfig,
    state: ProtocolState,
    field: str,
    expected: Any,
) -> bool:
    return all(
        lookup_value(state.local_fields(node), field) == expected
        for node in config.nodes
    )


def remove_selected_message(
    state: ProtocolState, event: RuntimeEvent
) -> ProtocolState:
    selected = message_for(event)
    messages = []
    removed = False
    for message in state.messages:
        if not removed and message.identifier == selected.identifier:
            removed = True
        else:
            messages.append(message)
    return replace(state, messages=tuple(messages))


def emit_many(
    state: ProtocolState,
    kind: str,
    sender: Any,
    receivers: Sequence[Any],
    payload: FieldStore,
) -> ProtocolState:
    emitted = tuple(
        Message(
            state.next_message_id + index,
            kind,
            sender,
            receiver,
            payload,
        )
        for index, receiver in enumerate(receivers)
    )
    return replace(
        state,
        messages=state.messages + emitted,
        next_message_id=state.next_message_id + len(receivers),
    )


def emit_one(
    state: ProtocolState,
    kind: str,
    sender: Any,
    receiver: Any,
    payload: FieldStore,
) -> ProtocolState:
    return emit_many(state, kind, sender, (receiver,), payload)


def run_schedule(
    *,
    initialize: Callable[[], ProtocolState],
    step: Callable[[ProtocolConfig, ProtocolState, ExternalEvent], Any],
    complete: Callable[[ProtocolConfig, ProtocolState], Optional[bool]],
    stuck: Callable[[ProtocolConfig, ProtocolState], Optional[bool]],
    config: ProtocolConfig,
    fuel: int,
    schedule: Sequence[ExternalEvent],
    state: Optional[ProtocolState] = None,
) -> RunOutcome:
    """Execute compiled transitions against a caller-supplied finite schedule."""

    if not isinstance(fuel, int) or isinstance(fuel, bool) or fuel < 0:
        raise ProtocolIRValidationError("fuel must be a natural number")
    current = initialize() if state is None else state
    steps = 0
    remaining = fuel
    position = 0
    while True:
        complete_result = complete(config, current)
        if complete_result is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="completion-predicate-malformed",
            )
        if complete_result:
            return RunOutcome(RunStatus.COMPLETE, current, steps)
        stuck_result = stuck(config, current)
        if stuck_result is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="stuck-predicate-malformed",
            )
        if stuck_result:
            return RunOutcome(RunStatus.STUCK, current, steps)
        if remaining == 0:
            return RunOutcome(RunStatus.BOUNDED, current, steps)
        if position == len(schedule):
            return RunOutcome(RunStatus.SCHEDULE_EXHAUSTED, current, steps)
        event = schedule[position]
        result = step(config, current, event)
        if isinstance(result, StepFailure):
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                event=event,
                error=f"transition-rejected:{result.error.value}",
            )
        current = result.state
        steps += 1
        remaining -= 1
        position += 1


def run_callback(
    *,
    initialize: Callable[[], ProtocolState],
    step: Callable[[ProtocolConfig, ProtocolState, ExternalEvent], Any],
    complete: Callable[[ProtocolConfig, ProtocolState], Optional[bool]],
    stuck: Callable[[ProtocolConfig, ProtocolState], Optional[bool]],
    config: ProtocolConfig,
    start_event: StartEvent,
    scheduler: Callable[[ProtocolState], int],
    delivery_event: Callable[[ProtocolState, int], DeliveryEvent],
    max_steps: int = 10_000,
    observer: Optional[
        Callable[[ProtocolState, int, Optional[ExternalEvent]], None]
    ] = None,
) -> RunOutcome:
    """Execute compiled transition functions with a caller-owned scheduler."""

    if (
        not isinstance(max_steps, int)
        or isinstance(max_steps, bool)
        or max_steps < 0
    ):
        raise ProtocolIRValidationError("max_steps must be a natural number")
    current = initialize()
    steps = 0
    if observer is not None:
        observer(current, steps, None)
    if max_steps == 0:
        return RunOutcome(RunStatus.BOUNDED, current, steps)

    started = step(config, current, start_event)
    if isinstance(started, StepFailure):
        return RunOutcome(
            RunStatus.INVALID,
            current,
            steps,
            event=start_event,
            error=f"transition-rejected:{started.error.value}",
        )
    current = started.state
    steps += 1
    if observer is not None:
        observer(current, steps, start_event)

    while True:
        complete_result = complete(config, current)
        if complete_result is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="completion-predicate-malformed",
            )
        if complete_result:
            return RunOutcome(RunStatus.COMPLETE, current, steps)
        stuck_result = stuck(config, current)
        if stuck_result is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="stuck-predicate-malformed",
            )
        if stuck_result:
            return RunOutcome(RunStatus.STUCK, current, steps)
        if steps >= max_steps:
            return RunOutcome(RunStatus.BOUNDED, current, steps)

        selected_id = scheduler(current)
        event = delivery_event(current, selected_id)
        result = step(config, current, event)
        if isinstance(result, StepFailure):
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                event=event,
                error=f"transition-rejected:{result.error.value}",
            )
        current = result.state
        steps += 1
        if observer is not None:
            observer(current, steps, event)


__all__ = [
    "COMPILED_RUNTIME_ABI_VERSION",
    "GENERATED_PROTOCOL_API_VERSION",
    "GENERATED_PROTOCOL_PUBLIC_NAMES",
    "GENERATED_PROTOCOL_SIGNATURES",
    "CompiledEvaluationFailure",
    "CompiledRuntimeCompatibilityError",
    "GeneratedProtocolInterfaceError",
    "QueryEvent",
    "ResolvedDelivery",
    "ResolvedStart",
    "RuleStatus",
    "all_nodes_local_equal",
    "delivery_certificates",
    "eager_and",
    "eager_or",
    "emit_many",
    "emit_one",
    "is_permutation",
    "lookup_value",
    "local_value",
    "make_config",
    "make_delivery_event",
    "make_start_event",
    "message_for",
    "option_get",
    "pattern_matches",
    "remove_first",
    "remove_selected_message",
    "resolve_event",
    "require_runtime_abi",
    "run_callback",
    "run_schedule",
    "runtime_store",
    "set_global",
    "set_local",
    "start_certificates",
    "validate_generated_protocol_api",
]
