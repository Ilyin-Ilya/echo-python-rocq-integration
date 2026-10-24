#!/usr/bin/env python3
"""Compatibility helpers for evaluating the temporary legacy Echo exports.

Maintained generation uses ``generate_echo_oracles_from_rocq.py`` and emits
literal data only.  The validators remain here temporarily while the old Rocq
IR is a migration oracle.  Invoking this historical command also delegates to
the data-only renderer and can no longer recreate the retired interpreter.
"""

from __future__ import annotations

import argparse
import hashlib
import pprint
import sys
from pathlib import Path
from typing import Sequence

if __package__ and __package__.startswith("tools."):
    from .. import rocq_codegen
else:
    TOOLS = Path(__file__).resolve().parent.parent
    if str(TOOLS) not in sys.path:
        sys.path.insert(0, str(TOOLS))
    import rocq_codegen

GenerationError = rocq_codegen.GenerationError
RocqStringExport = rocq_codegen.RocqStringExport
evaluate_string_exports = rocq_codegen.evaluate_string_exports
_find_coqtop = rocq_codegen.find_coqtop
_find_rocqlib = rocq_codegen.find_rocqlib
parse_sexpr = rocq_codegen.parse_sexpr
_write_or_check = rocq_codegen.write_or_check


EXPECTED_TAGS = (
    "start",
    "first-echo-nonleaf",
    "first-echo-leaf",
    "repeated-echo",
    "initiator-echo",
    "participant-ack-more",
    "participant-ack-final",
    "initiator-ack-more",
    "initiator-ack-final",
)
EXPECTED_VECTOR_NAMES = EXPECTED_TAGS + ("invalid-first-echo-nonleaf-order",)
EXPECTED_RUN_VECTOR_NAMES = (
    "two-node-complete",
    "star-left-first",
    "star-right-first",
    "singleton-complete",
    "started-stuck",
    "zero-fuel-bounded",
    "invalid-start",
)

def evaluate_rocq_exports(
    rocq_project: Path,
    coqtop: rocq_codegen.RocqReplCommand,
    rocqlib: Path | None,
) -> tuple[str, str, str]:
    theories = rocq_project / "theories"
    exports = (
        RocqStringExport(
            "echo_program_sexpr",
            theories / "EchoTransitionIRExport.vo",
            (
                theories / "EchoTransitionIR.v",
                theories / "EchoTransitionIRExport.v",
            ),
        ),
        RocqStringExport(
            "echo_evaluation_vectors_sexpr",
            theories / "EchoEvaluationVectorsExport.vo",
            (
                theories / "EchoExecutableTypes.v",
                theories / "EchoExecutableExamples.v",
                theories / "EchoEvaluationVectorsExport.v",
            ),
        ),
        RocqStringExport(
            "echo_run_vectors_sexpr",
            theories / "EchoRunnerVectorsExport.vo",
            (
                theories / "EchoRunner.v",
                theories / "EchoRunnerExamples.v",
                theories / "EchoRunnerVectorsExport.v",
            ),
        ),
    )
    evaluated = evaluate_string_exports(
        rocq_project=rocq_project,
        theories=theories,
        logical_root="EchoVerif",
        imports=(
            "EchoTransitionIRExport",
            "EchoEvaluationVectorsExport",
            "EchoRunnerVectorsExport",
        ),
        exports=exports,
        coqtop=coqtop,
        rocqlib=rocqlib,
        description="echo-algorithm-coq",
    )
    return evaluated[0], evaluated[1], evaluated[2]


def _unsupported(context: str, value) -> None:
    raise GenerationError(f"unsupported {context}: {value!r}")


def _validate_node_expression(expression, context: str) -> None:
    if expression not in {
        "initiator",
        "message-sender",
        "message-receiver",
        "event-parent",
    }:
        _unsupported(context, expression)


def _validate_nodes_expression(expression, context: str) -> None:
    if expression in {"empty-nodes", "ordered-nodes"}:
        return
    if not isinstance(expression, tuple) or not expression:
        _unsupported(context, expression)
    head = expression[0]
    if head in {"pending", "neighbors"} and len(expression) == 2:
        _validate_node_expression(expression[1], f"{context} node")
        return
    if head == "remove" and len(expression) == 3:
        _validate_node_expression(expression[1], f"{context} removed node")
        _validate_nodes_expression(expression[2], f"{context} source nodes")
        return
    _unsupported(context, expression)


def _validate_parent_expression(expression, context: str) -> None:
    if expression == "no-parent":
        return
    if (
        isinstance(expression, tuple)
        and len(expression) == 2
        and expression[0] in {"some-parent", "current-parent"}
    ):
        _validate_node_expression(expression[1], f"{context} node")
        return
    _unsupported(context, expression)


def _validate_process_expression(expression, context: str) -> None:
    if not isinstance(expression, tuple) or not expression:
        _unsupported(context, expression)
    head = expression[0]
    if head == "current-process" and len(expression) == 2:
        _validate_node_expression(expression[1], f"{context} node")
        return
    if head == "make-process" and len(expression) == 4:
        _validate_parent_expression(expression[1], f"{context} parent")
        _validate_nodes_expression(expression[2], f"{context} pending")
        if expression[3] not in {"true", "false"}:
            _unsupported(f"{context} finished flag", expression[3])
        return
    _unsupported(context, expression)


def _validate_outbound_expression(expression, context: str) -> None:
    if expression == "no-outbound":
        return
    if not isinstance(expression, tuple) or len(expression) != 3:
        _unsupported(context, expression)
    head, kind, target = expression
    if kind not in {"echo", "ack"}:
        _unsupported(f"{context} message kind", kind)
    if head == "one-outbound":
        _validate_node_expression(target, f"{context} receiver")
        return
    if head == "map-outbound":
        _validate_nodes_expression(target, f"{context} receivers")
        return
    _unsupported(context, expression)


def _validate_guard(guard, context: str) -> None:
    if guard in {"initial", "message-in-store"}:
        return
    if not isinstance(guard, tuple) or not guard:
        _unsupported(context, guard)
    head = guard[0]
    if head == "kind" and len(guard) == 2:
        if guard[1] not in {"echo", "ack"}:
            _unsupported(f"{context} message kind", guard[1])
        return
    if head in {"node-equal", "node-not-equal"} and len(guard) == 3:
        _validate_node_expression(guard[1], f"{context} left node")
        _validate_node_expression(guard[2], f"{context} right node")
        return
    if head in {"process-initial", "has-parent-or-finished"} and len(guard) == 2:
        _validate_node_expression(guard[1], f"{context} node")
        return
    if head == "permutation" and len(guard) == 3:
        _validate_nodes_expression(guard[1], f"{context} left nodes")
        _validate_nodes_expression(guard[2], f"{context} right nodes")
        return
    if head in {"nodes-empty", "nodes-nonempty"} and len(guard) == 2:
        _validate_nodes_expression(guard[1], f"{context} nodes")
        return
    if head == "started" and len(guard) == 2:
        if guard[1] not in {"true", "false"}:
            _unsupported(f"{context} boolean", guard[1])
        return
    if head == "finished" and len(guard) == 3:
        _validate_node_expression(guard[1], f"{context} node")
        if guard[2] not in {"true", "false"}:
            _unsupported(f"{context} boolean", guard[2])
        return
    if head == "parent-equal" and len(guard) == 3:
        _validate_node_expression(guard[1], f"{context} process node")
        _validate_parent_expression(guard[2], f"{context} expected parent")
        return
    if head == "node-in" and len(guard) == 3:
        _validate_node_expression(guard[1], f"{context} node")
        _validate_nodes_expression(guard[2], f"{context} nodes")
        return
    _unsupported(context, guard)


def _validate_action(action, context: str) -> None:
    if not isinstance(action, tuple) or not action:
        _unsupported(context, action)
    if action[0] == "start-action" and len(action) == 2:
        _validate_nodes_expression(action[1], f"{context} startup nodes")
        return
    if action[0] == "deliver-action" and len(action) == 3:
        _validate_process_expression(action[1], f"{context} process")
        _validate_outbound_expression(action[2], f"{context} outbound")
        return
    _unsupported(context, action)


def validate_program(program: tuple) -> None:
    if not program or program[0] != "program":
        raise GenerationError("the export must start with (program ...)")
    rules = program[1:]
    tags: list[str] = []
    for rule in rules:
        if not isinstance(rule, tuple) or len(rule) != 4 or rule[0] != "rule":
            raise GenerationError(f"malformed rule: {rule!r}")
        tag, guards, action = rule[1:]
        if not isinstance(tag, str):
            raise GenerationError(f"non-atomic rule tag: {tag!r}")
        if not isinstance(guards, tuple) or not guards or guards[0] != "guards":
            raise GenerationError(f"malformed guards for {tag}: {guards!r}")
        if len(guards) == 1:
            raise GenerationError(f"rule {tag} has no guards")
        for index, guard in enumerate(guards[1:], start=1):
            _validate_guard(guard, f"guard {index} for rule {tag}")
        _validate_action(action, f"action for rule {tag}")
        expected_action = "start-action" if tag == "start" else "deliver-action"
        if action[0] != expected_action:
            raise GenerationError(
                f"rule {tag} must use {expected_action}, got {action[0]}"
            )
        tags.append(tag)
    if tuple(tags) != EXPECTED_TAGS:
        raise GenerationError(
            f"unexpected rule order/tags: expected {EXPECTED_TAGS!r}, got {tuple(tags)!r}"
        )


def validate_evaluation_vectors(vectors: tuple) -> None:
    if len(vectors) < 2 or vectors[0] != "evaluation-vectors":
        raise GenerationError("the vector export must start with (evaluation-vectors ...)")
    config = vectors[1]
    if not isinstance(config, tuple) or len(config) != 4 or config[0] != "config":
        raise GenerationError(f"malformed evaluation config: {config!r}")
    nodes, adjacency = config[2], config[3]
    if not isinstance(nodes, tuple) or not nodes or nodes[0] != "nodes":
        raise GenerationError(f"malformed evaluation nodes: {nodes!r}")
    if not isinstance(adjacency, tuple) or not adjacency or adjacency[0] != "adjacency":
        raise GenerationError(f"malformed evaluation adjacency: {adjacency!r}")

    names: list[str] = []
    for vector in vectors[2:]:
        if not isinstance(vector, tuple) or len(vector) != 5 or vector[0] != "vector":
            raise GenerationError(f"malformed evaluation vector: {vector!r}")
        name, state, event, expected = vector[1:]
        if not isinstance(name, str):
            raise GenerationError(f"non-atomic evaluation-vector name: {name!r}")
        if not isinstance(state, tuple) or not state or state[0] != "state":
            raise GenerationError(f"malformed input state for {name}: {state!r}")
        if not isinstance(event, tuple) or not event or event[0] != "event":
            raise GenerationError(f"malformed event for {name}: {event!r}")
        if expected != "none" and (
            not isinstance(expected, tuple)
            or len(expected) != 2
            or expected[0] != "some"
            or not isinstance(expected[1], tuple)
            or not expected[1]
            or expected[1][0] != "state"
        ):
            raise GenerationError(f"malformed expected result for {name}: {expected!r}")
        names.append(name)
    if tuple(names) != EXPECTED_VECTOR_NAMES:
        raise GenerationError(
            "unexpected evaluation-vector order/names: "
            f"expected {EXPECTED_VECTOR_NAMES!r}, got {tuple(names)!r}"
        )


def validate_run_vectors(vectors: tuple) -> None:
    if not vectors or vectors[0] != "run-vectors":
        raise GenerationError("the run-vector export must start with (run-vectors ...)")

    names: list[str] = []
    for vector in vectors[1:]:
        if not isinstance(vector, tuple) or len(vector) != 7 or vector[0] != "run-vector":
            raise GenerationError(f"malformed run vector: {vector!r}")
        name, config, fuel, initial, schedule, expected = vector[1:]
        if not isinstance(name, str):
            raise GenerationError(f"non-atomic run-vector name: {name!r}")
        if not isinstance(config, tuple) or len(config) != 4 or config[0] != "config":
            raise GenerationError(f"malformed run config for {name}: {config!r}")
        if not isinstance(fuel, str) or not fuel.isdigit():
            raise GenerationError(f"malformed run fuel for {name}: {fuel!r}")
        if not isinstance(initial, tuple) or not initial or initial[0] != "state":
            raise GenerationError(f"malformed initial state for {name}: {initial!r}")
        if not isinstance(schedule, tuple) or not schedule or schedule[0] != "schedule":
            raise GenerationError(f"malformed schedule for {name}: {schedule!r}")
        for event in schedule[1:]:
            if not isinstance(event, tuple) or not event or event[0] != "event":
                raise GenerationError(f"malformed scheduled event for {name}: {event!r}")
        if not isinstance(expected, tuple) or not expected:
            raise GenerationError(f"malformed run result for {name}: {expected!r}")
        outcome = expected[0]
        expected_length = 4 if outcome == "invalid-choice" else 3
        if outcome not in {"complete", "stuck", "bounded", "invalid-choice"}:
            raise GenerationError(f"unknown run outcome for {name}: {outcome!r}")
        if len(expected) != expected_length:
            raise GenerationError(f"malformed {outcome} result for {name}: {expected!r}")
        if not isinstance(expected[1], str) or not expected[1].isdigit():
            raise GenerationError(f"malformed result step count for {name}: {expected[1]!r}")
        if not isinstance(expected[2], tuple) or not expected[2] or expected[2][0] != "state":
            raise GenerationError(f"malformed result state for {name}: {expected[2]!r}")
        if outcome == "invalid-choice":
            rejected = expected[3]
            if not isinstance(rejected, tuple) or not rejected or rejected[0] != "event":
                raise GenerationError(f"malformed rejected event for {name}: {rejected!r}")
        names.append(name)
    if tuple(names) != EXPECTED_RUN_VECTOR_NAMES:
        raise GenerationError(
            "unexpected run-vector order/names: "
            f"expected {EXPECTED_RUN_VECTOR_NAMES!r}, got {tuple(names)!r}"
        )


def render_python(
    program: tuple,
    sexpr: str,
    evaluation_vectors: tuple,
    evaluation_vectors_sexpr: str,
    run_vectors: tuple,
    run_vectors_sexpr: str,
) -> str:
    # Compatibility entry point.  The maintained artifact is data-only; keep
    # old callers safe while the validation helpers are moved out of this file.
    if __package__:
        from .generate_echo_oracles_from_rocq import render_oracle_data
    else:
        from generate_echo_oracles_from_rocq import render_oracle_data

    return render_oracle_data(
        program,
        sexpr,
        evaluation_vectors,
        evaluation_vectors_sexpr,
        run_vectors,
        run_vectors_sexpr,
    )

    # Retained unreachable template below is migration history and will be
    # deleted together with the old Rocq-specific IR/validator layer.
    digest = hashlib.sha256(sexpr.encode("utf-8")).hexdigest()
    vectors_digest = hashlib.sha256(
        evaluation_vectors_sexpr.encode("utf-8")
    ).hexdigest()
    run_vectors_digest = hashlib.sha256(
        run_vectors_sexpr.encode("utf-8")
    ).hexdigest()
    program_literal = pprint.pformat(program, width=88, compact=False, sort_dicts=False)
    vectors_literal = pprint.pformat(
        evaluation_vectors, width=88, compact=False, sort_dicts=False
    )
    run_vectors_literal = pprint.pformat(
        run_vectors, width=88, compact=False, sort_dicts=False
    )
    return f'''# Generated by tools/migration/legacy_echo_export.py; do not edit.
"""Executable Echo core generated from Rocq's proved first-order program.

``PROGRAM`` is the evaluated Rocq value that directly supplies ``echo_exec``
in ``EchoTransitionIR.v``.  There is no second handwritten Rocq transition
function behind it.  This module has no Rocq or OCaml runtime dependency.
The small interpreter below is the code-generation backend and remains part
of the trusted implementation boundary.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Callable, Generic, Hashable, Mapping, Optional, Sequence, Tuple, TypeVar


Node = TypeVar("Node", bound=Hashable)
ECHO = "ECHO"
ACK = "ACK"
RUN_COMPLETE = "complete"
RUN_STUCK = "stuck"
RUN_BOUNDED = "bounded"
RUN_INVALID_CHOICE = "invalid-choice"

ROCQ_PROGRAM_SHA256 = "{digest}"
ROCQ_PROGRAM_SEXPR = {sexpr!r}
PROGRAM = {program_literal}
ROCQ_EVALUATION_VECTORS_SHA256 = "{vectors_digest}"
ROCQ_EVALUATION_VECTORS_SEXPR = {evaluation_vectors_sexpr!r}
ROCQ_EVALUATION_VECTORS = {vectors_literal}
ROCQ_RUN_VECTORS_SHA256 = "{run_vectors_digest}"
ROCQ_RUN_VECTORS_SEXPR = {run_vectors_sexpr!r}
ROCQ_RUN_VECTORS = {run_vectors_literal}


@dataclass(frozen=True)
class Message(Generic[Node]):
    message_id: int
    kind: str
    sender: Node
    receiver: Node


@dataclass(frozen=True)
class Process(Generic[Node]):
    parent: Optional[Node] = None
    pending: Tuple[Node, ...] = ()
    finished: bool = False


@dataclass(frozen=True)
class State(Generic[Node]):
    roles: Mapping[Node, Process[Node]] = field(default_factory=dict)
    store: Tuple[Message[Node], ...] = ()
    started: bool = False
    next_message_id: int = 1

    def __post_init__(self) -> None:
        object.__setattr__(self, "roles", MappingProxyType(dict(self.roles)))


@dataclass(frozen=True)
class Config(Generic[Node]):
    initiator: Node
    nodes: Tuple[Node, ...]
    adjacency: Mapping[Node, Tuple[Node, ...]]


@dataclass(frozen=True)
class Event(Generic[Node]):
    tag: str
    message: Optional[Message[Node]] = None
    ordered_nodes: Tuple[Node, ...] = ()
    parent: Optional[Node] = None


@dataclass(frozen=True)
class RunResult(Generic[Node]):
    outcome: str
    state: State[Node]
    steps: int
    rejected_event: Optional[Event[Node]] = None
    rejected_message: Optional[Message[Node]] = None


INITIAL_PROCESS = Process()
RULES = {{rule[1]: rule for rule in PROGRAM[1:]}}


def _process(state: State[Node], node: Node) -> Process[Node]:
    return state.roles.get(node, INITIAL_PROCESS)


def _message(event: Event[Node]) -> Message[Node]:
    if event.message is None:
        raise ValueError("this event requires a message")
    return event.message


def _event_parent(event: Event[Node]) -> Node:
    if event.parent is None:
        raise ValueError("this event requires a parent certificate")
    return event.parent


def _neighbors(config: Config[Node], node: Node) -> Tuple[Node, ...]:
    adjacent = config.adjacency.get(node, ())
    return tuple(candidate for candidate in config.nodes if candidate in adjacent)


def _remove_first(item: Node, items: Tuple[Node, ...]) -> Tuple[Node, ...]:
    result = list(items)
    try:
        result.remove(item)
    except ValueError:
        pass
    return tuple(result)


def _permutation_equal(left: Tuple[Node, ...], right: Tuple[Node, ...]) -> bool:
    remaining = list(right)
    for item in left:
        try:
            remaining.remove(item)
        except ValueError:
            return False
    return not remaining


def _eval_node(config: Config[Node], event: Event[Node], expr):
    if expr == "initiator":
        return config.initiator
    if expr == "message-sender":
        return _message(event).sender
    if expr == "message-receiver":
        return _message(event).receiver
    if expr == "event-parent":
        return _event_parent(event)
    raise ValueError(f"unknown node expression: {{expr!r}}")


def _eval_nodes(config: Config[Node], state: State[Node], event: Event[Node], expr):
    if expr == "empty-nodes":
        return ()
    if expr == "ordered-nodes":
        return event.ordered_nodes
    head = expr[0]
    if head == "pending":
        return _process(state, _eval_node(config, event, expr[1])).pending
    if head == "neighbors":
        return _neighbors(config, _eval_node(config, event, expr[1]))
    if head == "remove":
        return _remove_first(
            _eval_node(config, event, expr[1]),
            _eval_nodes(config, state, event, expr[2]),
        )
    raise ValueError(f"unknown nodes expression: {{expr!r}}")


def _eval_parent(config: Config[Node], state: State[Node], event: Event[Node], expr):
    if expr == "no-parent":
        return None
    if expr[0] == "some-parent":
        return _eval_node(config, event, expr[1])
    if expr[0] == "current-parent":
        return _process(state, _eval_node(config, event, expr[1])).parent
    raise ValueError(f"unknown parent expression: {{expr!r}}")


def _eval_process(config: Config[Node], state: State[Node], event: Event[Node], expr):
    if expr[0] == "current-process":
        return _process(state, _eval_node(config, event, expr[1]))
    if expr[0] == "make-process":
        return Process(
            parent=_eval_parent(config, state, event, expr[1]),
            pending=_eval_nodes(config, state, event, expr[2]),
            finished=expr[3] == "true",
        )
    raise ValueError(f"unknown process expression: {{expr!r}}")


def _eval_outbound(config: Config[Node], state: State[Node], event: Event[Node], expr):
    if expr == "no-outbound":
        return ()
    head, kind = expr[0], ECHO if expr[1] == "echo" else ACK
    if head == "one-outbound":
        return ((kind, _eval_node(config, event, expr[2])),)
    if head == "map-outbound":
        return tuple(
            (kind, receiver)
            for receiver in _eval_nodes(config, state, event, expr[2])
        )
    raise ValueError(f"unknown outbound expression: {{expr!r}}")


def _is_initial(config: Config[Node], state: State[Node]) -> bool:
    return (
        not state.started
        and not state.store
        and state.next_message_id == 1
        and all(_process(state, node) == INITIAL_PROCESS for node in config.nodes)
    )


def _guard_holds(config: Config[Node], state: State[Node], event: Event[Node], guard) -> bool:
    if guard == "initial":
        return _is_initial(config, state)
    if guard == "message-in-store":
        return _message(event) in state.store
    head = guard[0]
    if head == "kind":
        expected = ECHO if guard[1] == "echo" else ACK
        return _message(event).kind == expected
    if head == "node-equal":
        return _eval_node(config, event, guard[1]) == _eval_node(config, event, guard[2])
    if head == "node-not-equal":
        return _eval_node(config, event, guard[1]) != _eval_node(config, event, guard[2])
    if head == "process-initial":
        return _process(state, _eval_node(config, event, guard[1])) == INITIAL_PROCESS
    if head == "permutation":
        return _permutation_equal(
            _eval_nodes(config, state, event, guard[1]),
            _eval_nodes(config, state, event, guard[2]),
        )
    if head == "nodes-empty":
        return not _eval_nodes(config, state, event, guard[1])
    if head == "nodes-nonempty":
        return bool(_eval_nodes(config, state, event, guard[1]))
    if head == "has-parent-or-finished":
        process = _process(state, _eval_node(config, event, guard[1]))
        return process.parent is not None or process.finished
    if head == "started":
        return state.started == (guard[1] == "true")
    if head == "finished":
        return _process(
            state, _eval_node(config, event, guard[1])
        ).finished == (guard[2] == "true")
    if head == "parent-equal":
        return _process(
            state, _eval_node(config, event, guard[1])
        ).parent == _eval_parent(config, state, event, guard[2])
    if head == "node-in":
        return _eval_node(config, event, guard[1]) in _eval_nodes(
            config, state, event, guard[2]
        )
    raise ValueError(f"unknown guard: {{guard!r}}")


def _materialize(next_id: int, sender: Node, outbound):
    return tuple(
        Message(next_id + offset, kind, sender, receiver)
        for offset, (kind, receiver) in enumerate(outbound)
    )


def _remove_message(message_id: int, store: Tuple[Message[Node], ...]):
    result = list(store)
    for index, message in enumerate(result):
        if message.message_id == message_id:
            del result[index]
            break
    return tuple(result)


def _apply_action(config: Config[Node], state: State[Node], event: Event[Node], action):
    if action[0] == "start-action":
        ordered = _eval_nodes(config, state, event, action[1])
        outbound = tuple((ECHO, neighbor) for neighbor in ordered)
        roles = dict(state.roles)
        roles[config.initiator] = Process(None, ordered, False)
        emitted = _materialize(state.next_message_id, config.initiator, outbound)
        return State(roles, state.store + emitted, True, state.next_message_id + len(outbound))
    if action[0] == "deliver-action":
        message = _message(event)
        new_process = _eval_process(config, state, event, action[1])
        outbound = _eval_outbound(config, state, event, action[2])
        roles = dict(state.roles)
        roles[message.receiver] = new_process
        emitted = _materialize(state.next_message_id, message.receiver, outbound)
        return State(
            roles,
            _remove_message(message.message_id, state.store) + emitted,
            state.started,
            state.next_message_id + len(outbound),
        )
    raise ValueError(f"unknown action: {{action!r}}")


def echo_exec(
    config: Config[Node], state: State[Node], event: Event[Node]
) -> Optional[State[Node]]:
    """Return the successor selected by the generated Rocq program, or ``None``."""

    rule = RULES.get(event.tag)
    if rule is None:
        return None
    guards, action = rule[2], rule[3]
    try:
        if not all(
            _guard_holds(config, state, event, guard) for guard in guards[1:]
        ):
            return None
        return _apply_action(config, state, event, action)
    except (KeyError, TypeError, ValueError):
        return None


def start(
    config: Config[Node],
    state: State[Node],
    ordered_nodes: Optional[Tuple[Node, ...]] = None,
) -> Optional[State[Node]]:
    """Execute startup using a permutation certificate supplied by the adapter."""

    if ordered_nodes is None:
        ordered_nodes = _neighbors(config, config.initiator)
    return echo_exec(config, state, Event("start", ordered_nodes=ordered_nodes))


def event_for_message(
    config: Config[Node],
    state: State[Node],
    message: Message[Node],
    ordered_nodes: Optional[Tuple[Node, ...]] = None,
) -> Optional[Event[Node]]:
    """Build the unique accepted delivery event for a queued message."""

    if message not in state.store:
        return None
    if ordered_nodes is None:
        ordered_nodes = _remove_first(
            message.sender, _neighbors(config, message.receiver)
        )
    parent = _process(state, message.receiver).parent
    for rule in PROGRAM[2:]:
        event = Event(rule[1], message, ordered_nodes, parent)
        if echo_exec(config, state, event) is not None:
            return event
    return None


def deliver(
    config: Config[Node],
    state: State[Node],
    message: Message[Node],
    ordered_nodes: Optional[Tuple[Node, ...]] = None,
) -> Optional[State[Node]]:
    """Select and execute the unique valid delivery rule from the generated program."""

    event = event_for_message(config, state, message, ordered_nodes)
    return None if event is None else echo_exec(config, state, event)


def is_complete(config: Config[Node], state: State[Node]) -> bool:
    """The generated form of Rocq's singleton-aware ``echo_completeb``."""

    root = _process(state, config.initiator)
    return (
        state.started
        and not root.pending
        and not state.store
        and (root.finished or not _neighbors(config, config.initiator))
    )


def _is_stuck(state: State[Node]) -> bool:
    return state.started and not state.store


def run_schedule(
    config: Config[Node],
    state: State[Node],
    schedule: Sequence[Event[Node]],
    fuel: int,
) -> RunResult[Node]:
    """Execute the exact bounded schedule semantics exported from Rocq."""

    if fuel < 0:
        raise ValueError("fuel must be non-negative")
    current = state
    steps = 0
    schedule_index = 0
    while True:
        if is_complete(config, current):
            return RunResult(RUN_COMPLETE, current, steps)
        if _is_stuck(current):
            return RunResult(RUN_STUCK, current, steps)
        if steps >= fuel or schedule_index >= len(schedule):
            return RunResult(RUN_BOUNDED, current, steps)
        event = schedule[schedule_index]
        successor = echo_exec(config, current, event)
        if successor is None:
            return RunResult(RUN_INVALID_CHOICE, current, steps, event)
        current = successor
        steps += 1
        schedule_index += 1


def run(
    config: Config[Node],
    scheduler: Callable[[State[Node]], Message[Node]],
    max_steps: int = 10_000,
    observer: Optional[
        Callable[[State[Node], int, Optional[Event[Node]]], None]
    ] = None,
    ordered_start: Optional[Tuple[Node, ...]] = None,
) -> RunResult[Node]:
    """Run from canonical initialization with an environment scheduler.

    The callback can choose only a message.  This module derives its event
    certificate and successor; neither the scheduler nor observer can install
    or mutate state.
    """

    if max_steps < 0:
        raise ValueError("max_steps must be non-negative")
    current: State[Node] = State()
    steps = 0
    if observer is not None:
        observer(current, steps, None)
    if max_steps == 0:
        return RunResult(RUN_BOUNDED, current, steps)

    start_event = Event(
        "start",
        ordered_nodes=(
            _neighbors(config, config.initiator)
            if ordered_start is None
            else ordered_start
        ),
    )
    successor = echo_exec(config, current, start_event)
    if successor is None:
        return RunResult(RUN_INVALID_CHOICE, current, steps, start_event)
    current = successor
    steps += 1
    if observer is not None:
        observer(current, steps, start_event)

    while True:
        if is_complete(config, current):
            return RunResult(RUN_COMPLETE, current, steps)
        if _is_stuck(current):
            return RunResult(RUN_STUCK, current, steps)
        if steps >= max_steps:
            return RunResult(RUN_BOUNDED, current, steps)
        selected_message = scheduler(current)
        event = event_for_message(config, current, selected_message)
        if event is None:
            return RunResult(
                RUN_INVALID_CHOICE,
                current,
                steps,
                rejected_message=selected_message,
            )
        successor = echo_exec(config, current, event)
        if successor is None:
            return RunResult(RUN_INVALID_CHOICE, current, steps, event)
        current = successor
        steps += 1
        if observer is not None:
            observer(current, steps, event)


'''


def main(argv: Sequence[str] | None = None) -> int:
    repository = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rocq-project",
        type=Path,
        default=repository.parent / "echo-algorithm-coq",
    )
    parser.add_argument(
        "--sexpr-output",
        type=Path,
        default=repository / "bridge" / "rocq_echo_program.sexp",
    )
    parser.add_argument(
        "--python-output",
        type=Path,
        default=repository
        / "distributed_simulations"
        / "migration"
        / "generated_echo_oracles.py",
    )
    parser.add_argument(
        "--vectors-output",
        type=Path,
        default=repository / "bridge" / "rocq_echo_vectors.sexp",
    )
    parser.add_argument(
        "--run-vectors-output",
        type=Path,
        default=repository / "bridge" / "rocq_echo_run_vectors.sexp",
    )
    parser.add_argument("--coqtop")
    parser.add_argument("--rocqlib")
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args(argv)

    try:
        coqtop = _find_coqtop(arguments.coqtop)
        rocqlib = _find_rocqlib(arguments.rocqlib)
        sexpr, vectors_sexpr, run_vectors_sexpr = evaluate_rocq_exports(
            arguments.rocq_project.resolve(), coqtop, rocqlib
        )
        program = parse_sexpr(sexpr)
        vectors = parse_sexpr(vectors_sexpr)
        run_vectors = parse_sexpr(run_vectors_sexpr)
        validate_program(program)
        validate_evaluation_vectors(vectors)
        validate_run_vectors(run_vectors)
        python_source = render_python(
            program,
            sexpr,
            vectors,
            vectors_sexpr,
            run_vectors,
            run_vectors_sexpr,
        )
    except (GenerationError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    sexpr_current = _write_or_check(
        arguments.sexpr_output.resolve(), sexpr + "\n", arguments.check
    )
    vectors_current = _write_or_check(
        arguments.vectors_output.resolve(), vectors_sexpr + "\n", arguments.check
    )
    run_vectors_current = _write_or_check(
        arguments.run_vectors_output.resolve(),
        run_vectors_sexpr + "\n",
        arguments.check,
    )
    python_current = _write_or_check(
        arguments.python_output.resolve(), python_source, arguments.check
    )
    if (
        not sexpr_current
        or not vectors_current
        or not run_vectors_current
        or not python_current
    ):
        stale = []
        if not sexpr_current:
            stale.append(str(arguments.sexpr_output))
        if not vectors_current:
            stale.append(str(arguments.vectors_output))
        if not run_vectors_current:
            stale.append(str(arguments.run_vectors_output))
        if not python_current:
            stale.append(str(arguments.python_output))
        print("generated Rocq-to-Python artifacts are stale: " + ", ".join(stale), file=sys.stderr)
        return 1

    digest = hashlib.sha256(sexpr.encode("utf-8")).hexdigest()
    vectors_digest = hashlib.sha256(vectors_sexpr.encode("utf-8")).hexdigest()
    run_vectors_digest = hashlib.sha256(
        run_vectors_sexpr.encode("utf-8")
    ).hexdigest()
    mode = "verified" if arguments.check else "generated"
    print(
        f"{mode} {len(program) - 1} Rocq rules and {len(vectors) - 2} "
        f"evaluation vectors and {len(run_vectors) - 1} run vectors "
        f"(program {digest}, vectors {vectors_digest}, runs {run_vectors_digest})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
