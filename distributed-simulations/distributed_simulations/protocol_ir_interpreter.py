"""Protocol-neutral reference interpreter for the typed protocol IR.

This module executes typed AST programs.  Production generated protocols use
``protocol_compiled_runtime`` instead; this interpreter remains an independent
conformance and migration path.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, Mapping, Optional, Sequence, Tuple

from .protocol_ir_ast import (
    Action,
    EventPattern,
    Expression,
    ProtocolProgram,
    Rule,
    RuntimeContract,
)
from .protocol_values import (
    DeliveryEvent,
    ExternalEvent,
    FieldStore,
    IRType,
    IRValue,
    Message,
    Node,
    ProtocolConfig,
    ProtocolIRValidationError,
    ProtocolState,
    RunOutcome,
    RunStatus,
    StartEvent,
    StepError,
    StepFailure,
    StepResult,
    StepSuccess,
    runtime_store,
    runtime_value,
    validate_field_store,
    validate_message_id,
)

@dataclass(frozen=True)
class _QueryEvent:
    pass


@dataclass(frozen=True)
class _RuntimeStart:
    certificates: FieldStore


@dataclass(frozen=True)
class _RuntimeDelivery:
    message: Message
    certificates: FieldStore


RuntimeEvent = Any


class _EvaluationFailure(RuntimeError):
    pass



def runtime_contract(program: ProtocolProgram) -> RuntimeContract:
    """Describe the typed hooks that a human adapter must implement.

    The function intentionally does not generate topology parsing, scheduling,
    certificate policy, logging, or application I/O. Those remain explicit
    integration choices, while protocol transitions stay interpreter-owned.
    """

    signature = program.signature
    return RuntimeContract(
        protocol_id=program.protocol_id,
        schema_version=program.schema_version,
        ir_version=program.ir_version,
        config_fields=signature.config_fields,
        start_certificate_fields=signature.start_certificate_fields,
        delivery_certificate_fields=signature.delivery_certificate_fields,
        message_kinds=signature.message_kinds,
        payload_fields=signature.payload_fields,
        diagnostic_rule_ids=signature.rule_ids,
    )


def _lookup(store: FieldStore, field: str) -> IRValue:
    for candidate, value in store:
        if candidate == field:
            return value
    raise _EvaluationFailure(f"missing field {field!r}")


def _set_field(store: FieldStore, field: str, value: IRValue) -> FieldStore:
    updated = []
    found = False
    for candidate, old in store:
        if candidate == field:
            updated.append((candidate, value))
            found = True
        else:
            updated.append((candidate, old))
    if not found:
        raise _EvaluationFailure(f"missing field {field!r}")
    return tuple(updated)


def _set_local(state: ProtocolState, node: Node, field: str, value: IRValue) -> ProtocolState:
    fields = _set_field(state.local_fields(node), field, value)
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


def _remove_first(value: Node, items: Sequence[Node]) -> Tuple[Node, ...]:
    result = []
    removed = False
    for item in items:
        if not removed and item == value:
            removed = True
        else:
            result.append(item)
    return tuple(result)


def _is_permutation(left: Sequence[Node], right: Sequence[Node]) -> bool:
    residual = list(right)
    for item in left:
        try:
            index = residual.index(item)
        except ValueError:
            return False
        residual.pop(index)
    return not residual


def _message_for(event: RuntimeEvent) -> Message:
    if not isinstance(event, _RuntimeDelivery):
        raise _EvaluationFailure("expression requires a delivery event")
    return event.message


def evaluate_expression(
    expression: Expression,
    config: ProtocolConfig,
    state: ProtocolState,
    event: RuntimeEvent,
) -> IRValue:
    """Evaluate one already type-checked expression."""

    op = expression.operator
    args = expression.arguments
    if op == "literal":
        return args[0]
    if op == "config":
        return _lookup(config.fields, args[0])
    if op == "global":
        return _lookup(state.globals, args[0])
    if op == "local":
        process = evaluate_expression(args[0], config, state, event).value
        return _lookup(state.local_fields(process), args[1])
    if op == "option-some":
        return IRValue(IRType.OPTION_NODE, evaluate_expression(args[0], config, state, event).value)
    if op == "option-get":
        value = evaluate_expression(args[0], config, state, event).value
        if value is None:
            raise _EvaluationFailure("option-get requires Some(node)")
        return IRValue(IRType.NODE, value)
    if op == "message-id":
        return IRValue(IRType.NAT, _message_for(event).identifier)
    if op == "message-sender":
        return IRValue(IRType.NODE, _message_for(event).sender)
    if op == "message-receiver":
        return IRValue(IRType.NODE, _message_for(event).receiver)
    if op == "message-kind-is":
        return IRValue(IRType.BOOL, _message_for(event).kind == args[0])
    if op == "payload":
        return _lookup(_message_for(event).payload, args[0])
    if op == "start-certificate":
        if not isinstance(event, _RuntimeStart):
            raise _EvaluationFailure("start certificate read outside startup")
        return _lookup(event.certificates, args[0])
    if op == "delivery-certificate":
        if not isinstance(event, _RuntimeDelivery):
            raise _EvaluationFailure("delivery certificate read outside delivery")
        return _lookup(event.certificates, args[0])
    if op == "is-start":
        return IRValue(IRType.BOOL, isinstance(event, _RuntimeStart))
    if op == "is-delivery":
        return IRValue(IRType.BOOL, isinstance(event, _RuntimeDelivery))
    if op == "message-store-empty":
        return IRValue(IRType.BOOL, not state.messages)
    if op == "message-store-length":
        return IRValue(IRType.NAT, len(state.messages))
    if op == "next-message-id":
        return IRValue(IRType.NAT, state.next_message_id)
    if op == "neighbors":
        process = evaluate_expression(args[0], config, state, event).value
        return IRValue(IRType.LIST_NODE, config.neighbors_of(process))
    if op == "not":
        return IRValue(IRType.BOOL, not evaluate_expression(args[0], config, state, event).value)
    if op in ("and", "or"):
        # Rocq evaluates both operands before matching their results.
        left = evaluate_expression(args[0], config, state, event).value
        right = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.BOOL, left and right if op == "and" else left or right)
    if op == "equal":
        left = evaluate_expression(args[0], config, state, event)
        right = evaluate_expression(args[1], config, state, event)
        return IRValue(IRType.BOOL, left == right)
    if op == "option-is-some":
        return IRValue(IRType.BOOL, evaluate_expression(args[0], config, state, event).value is not None)
    if op == "list-is-empty":
        return IRValue(IRType.BOOL, not evaluate_expression(args[0], config, state, event).value)
    if op == "list-contains":
        item = evaluate_expression(args[0], config, state, event).value
        items = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.BOOL, item in items)
    if op == "list-remove":
        item = evaluate_expression(args[0], config, state, event).value
        items = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.LIST_NODE, _remove_first(item, items))
    if op == "list-append":
        left = evaluate_expression(args[0], config, state, event).value
        right = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.LIST_NODE, tuple(left) + tuple(right))
    if op == "list-permutation":
        left = evaluate_expression(args[0], config, state, event).value
        right = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.BOOL, _is_permutation(left, right))
    if op == "list-length":
        return IRValue(IRType.NAT, len(evaluate_expression(args[0], config, state, event).value))
    if op == "nat-add":
        left = evaluate_expression(args[0], config, state, event).value
        right = evaluate_expression(args[1], config, state, event).value
        return IRValue(IRType.NAT, left + right)
    if op == "nat-succ":
        return IRValue(IRType.NAT, evaluate_expression(args[0], config, state, event).value + 1)
    if op == "all-nodes-local-equal":
        expected = evaluate_expression(args[1], config, state, event)
        return IRValue(
            IRType.BOOL,
            all(_lookup(state.local_fields(node), args[0]) == expected for node in config.nodes),
        )
    raise _EvaluationFailure(f"unknown expression {op!r}")


def _evaluate_payload(
    payload: Sequence[Tuple[str, Expression]],
    config: ProtocolConfig,
    state: ProtocolState,
    event: RuntimeEvent,
) -> FieldStore:
    return tuple(
        (field, evaluate_expression(expression, config, state, event))
        for field, expression in payload
    )


def _emit(
    state: ProtocolState,
    kind: str,
    sender: Node,
    receivers: Sequence[Node],
    payload: FieldStore,
) -> ProtocolState:
    emitted = tuple(
        Message(state.next_message_id + index, kind, sender, receiver, payload)
        for index, receiver in enumerate(receivers)
    )
    return replace(
        state,
        messages=state.messages + emitted,
        next_message_id=state.next_message_id + len(receivers),
    )


def evaluate_action(
    action: Action,
    config: ProtocolConfig,
    state: ProtocolState,
    event: RuntimeEvent,
) -> ProtocolState:
    op = action.operator
    args = action.arguments
    if op == "skip":
        return state
    if op == "set-global":
        value = evaluate_expression(args[1], config, state, event)
        return replace(state, globals=_set_field(state.globals, args[0], value))
    if op == "set-local":
        process = evaluate_expression(args[0], config, state, event).value
        value = evaluate_expression(args[2], config, state, event)
        return _set_local(state, process, args[1], value)
    if op == "remove-selected-message":
        message = _message_for(event)
        messages = []
        removed = False
        for candidate in state.messages:
            if not removed and candidate.identifier == message.identifier:
                removed = True
            else:
                messages.append(candidate)
        return replace(state, messages=tuple(messages))
    if op in ("emit", "emit-many"):
        kind, sender_expr, receiver_expr, payload_exprs = args
        sender = evaluate_expression(sender_expr, config, state, event).value
        selected = evaluate_expression(receiver_expr, config, state, event).value
        receivers = (selected,) if op == "emit" else selected
        payload = _evaluate_payload(payload_exprs, config, state, event)
        return _emit(state, kind, sender, receivers, payload)
    if op == "sequence":
        successor = evaluate_action(args[0], config, state, event)
        return evaluate_action(args[1], config, successor, event)
    raise _EvaluationFailure(f"unknown action {op!r}")


def initialize_protocol(program: ProtocolProgram) -> ProtocolState:
    return ProtocolState(
        default_local=program.initial_local,
        local_overrides=(),
        messages=(),
        globals=program.initial_global,
        next_message_id=program.initial_next_message_id,
    )


def make_config(
    program: ProtocolProgram,
    *,
    nodes: Sequence[Node],
    neighbors: Mapping[Node, Sequence[Node]],
    fields: Mapping[str, Any],
) -> ProtocolConfig:
    return ProtocolConfig(
        nodes=tuple(nodes),
        neighbors=tuple((node, tuple(adjacent)) for node, adjacent in neighbors.items()),
        fields=runtime_store(program.signature.config_fields, fields),
    )


def make_start_event(program: ProtocolProgram, certificates: Mapping[str, Any]) -> StartEvent:
    return StartEvent(runtime_store(program.signature.start_certificate_fields, certificates))


def make_delivery_event(
    program: ProtocolProgram,
    message_id: int,
    certificates: Mapping[str, Any],
) -> DeliveryEvent:
    validate_message_id(message_id)
    return DeliveryEvent(
        message_id,
        runtime_store(program.signature.delivery_certificate_fields, certificates),
    )


def _resolve_event(
    program: ProtocolProgram,
    state: ProtocolState,
    event: ExternalEvent,
) -> Optional[RuntimeEvent]:
    if isinstance(event, StartEvent):
        validate_field_store(
            program.signature.start_certificate_fields, event.certificates
        )
        return _RuntimeStart(event.certificates)
    if isinstance(event, DeliveryEvent):
        validate_message_id(event.message_id)
        validate_field_store(
            program.signature.delivery_certificate_fields, event.certificates
        )
        for message in state.messages:
            if message.identifier == event.message_id:
                return _RuntimeDelivery(message, event.certificates)
        return None
    raise ProtocolIRValidationError(f"unknown external event {event!r}")


def _pattern_matches(pattern: EventPattern, event: RuntimeEvent) -> bool:
    if pattern.kind == "start":
        return isinstance(event, _RuntimeStart)
    return (
        isinstance(event, _RuntimeDelivery)
        and pattern.message_kind == event.message.kind
    )


def _rule_status(
    rule: Rule,
    config: ProtocolConfig,
    state: ProtocolState,
    event: RuntimeEvent,
) -> str:
    if not _pattern_matches(rule.pattern, event):
        return "mismatch"
    try:
        for guard in rule.guards:
            if not evaluate_expression(guard, config, state, event).value:
                return "disabled"
    except _EvaluationFailure:
        return "malformed"
    return "enabled"


def interpret_step(
    program: ProtocolProgram,
    config: ProtocolConfig,
    state: ProtocolState,
    external_event: ExternalEvent,
) -> StepResult:
    runtime_event = _resolve_event(program, state, external_event)
    if runtime_event is None:
        return StepFailure(StepError.UNQUEUED_MESSAGE)
    enabled = []
    for rule in program.rules:
        status = _rule_status(rule, config, state, runtime_event)
        if status == "malformed":
            return StepFailure(StepError.MALFORMED_GUARD)
        if status == "enabled":
            enabled.append(rule)
    if not enabled:
        return StepFailure(StepError.NO_ENABLED_RULE)
    if len(enabled) != 1:
        return StepFailure(StepError.AMBIGUOUS_ENABLED_RULES)
    selected = enabled[0]
    try:
        successor = evaluate_action(selected.action, config, state, runtime_event)
    except _EvaluationFailure:
        return StepFailure(StepError.MALFORMED_ACTION)
    return StepSuccess(selected.identifier, successor)


def evaluate_state_predicate(
    expression: Expression,
    config: ProtocolConfig,
    state: ProtocolState,
) -> Optional[bool]:
    try:
        return bool(evaluate_expression(expression, config, state, _QueryEvent()).value)
    except _EvaluationFailure:
        return None


def run_schedule(
    program: ProtocolProgram,
    config: ProtocolConfig,
    fuel: int,
    schedule: Sequence[ExternalEvent],
    state: Optional[ProtocolState] = None,
) -> RunOutcome:
    if not isinstance(fuel, int) or isinstance(fuel, bool) or fuel < 0:
        raise ProtocolIRValidationError("fuel must be a natural number")
    current = initialize_protocol(program) if state is None else state
    steps = 0
    remaining = fuel
    position = 0
    while True:
        complete = evaluate_state_predicate(program.complete, config, current)
        if complete is None:
            return RunOutcome(RunStatus.INVALID, current, steps, error="completion-predicate-malformed")
        if complete:
            return RunOutcome(RunStatus.COMPLETE, current, steps)
        stuck = evaluate_state_predicate(program.stuck, config, current)
        if stuck is None:
            return RunOutcome(RunStatus.INVALID, current, steps, error="stuck-predicate-malformed")
        if stuck:
            return RunOutcome(RunStatus.STUCK, current, steps)
        if remaining == 0:
            return RunOutcome(RunStatus.BOUNDED, current, steps)
        if position == len(schedule):
            return RunOutcome(RunStatus.SCHEDULE_EXHAUSTED, current, steps)
        event = schedule[position]
        result = interpret_step(program, config, current, event)
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
    program: ProtocolProgram,
    config: ProtocolConfig,
    *,
    start_event: StartEvent,
    scheduler: Callable[[ProtocolState], int],
    delivery_event: Callable[[ProtocolState, int], DeliveryEvent],
    max_steps: int = 10_000,
    observer: Optional[
        Callable[[ProtocolState, int, Optional[ExternalEvent]], None]
    ] = None,
) -> RunOutcome:
    """Run the generated computation frame with human-supplied hooks.

    The caller supplies configuration, startup certificates, a scheduling
    policy returning only a queued message identifier, a typed delivery-
    certificate factory, and optionally an observer for logging or UI work.
    ``interpret_step`` alone selects the rule and constructs the successor.
    This automates protocol execution without pretending to generate the whole
    application.
    """

    if (
        not isinstance(max_steps, int)
        or isinstance(max_steps, bool)
        or max_steps < 0
    ):
        raise ProtocolIRValidationError("max_steps must be a natural number")
    current = initialize_protocol(program)
    steps = 0
    if observer is not None:
        observer(current, steps, None)
    if max_steps == 0:
        return RunOutcome(RunStatus.BOUNDED, current, steps)

    started = interpret_step(program, config, current, start_event)
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
        complete = evaluate_state_predicate(program.complete, config, current)
        if complete is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="completion-predicate-malformed",
            )
        if complete:
            return RunOutcome(RunStatus.COMPLETE, current, steps)
        stuck = evaluate_state_predicate(program.stuck, config, current)
        if stuck is None:
            return RunOutcome(
                RunStatus.INVALID,
                current,
                steps,
                error="stuck-predicate-malformed",
            )
        if stuck:
            return RunOutcome(RunStatus.STUCK, current, steps)
        if steps >= max_steps:
            return RunOutcome(RunStatus.BOUNDED, current, steps)

        selected_id = scheduler(current)
        event = delivery_event(current, selected_id)
        result = interpret_step(program, config, current, event)
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
    "evaluate_action",
    "evaluate_expression",
    "evaluate_state_predicate",
    "initialize_protocol",
    "interpret_step",
    "make_config",
    "make_delivery_event",
    "make_start_event",
    "run_callback",
    "run_schedule",
    "runtime_contract",
]
