"""Scheduling and trace plumbing for the generated Echo executable.

This module chooses only which queued message identifier is delivered next.
All protocol decisions and state transitions remain in
``generated_echo_executable``.
"""

from __future__ import annotations

import random
from pathlib import Path
from typing import Any, Callable, Literal, Mapping, Optional, Tuple, Union

from ..protocol_values import (
    ExternalEvent,
    Message,
    ProtocolConfig,
    ProtocolState,
    RunOutcome,
    StartEvent,
)
from ..runtime import EventLog, RoleId
from . import generated_echo_executable
from .echo_codec import snapshot_from_protocol_state


SchedulerPolicy = Literal["random", "fifo", "lifo"]
MessageSelector = Callable[[Tuple[Message, ...]], int]
Scheduler = Union[SchedulerPolicy, MessageSelector]
EventCallback = Callable[[Mapping[str, Any]], None]


class SchedulerChoiceError(ValueError):
    """A custom scheduler did not identify a queued message."""


def _public_message_kind(kind: str) -> str:
    try:
        return {"request": "ECHO", "reply": "ACK"}[kind]
    except KeyError as error:
        raise ValueError(f"unknown generated Echo message kind {kind!r}") from error


def _parent(state: ProtocolState, node: RoleId) -> Optional[RoleId]:
    return dict(state.local_fields(node))["parent"].value


def _emit_new_messages(
    log: EventLog,
    before: ProtocolState,
    after: ProtocolState,
) -> None:
    for message in after.messages:
        if message.identifier < before.next_message_id:
            continue
        log.emit(
            "enqueue",
            message_id=message.identifier,
            kind=_public_message_kind(message.kind),
            sender=str(message.sender),
            receiver=str(message.receiver),
            payload={},
        )


def _emit_new_tree_edges(
    log: EventLog,
    config: ProtocolConfig,
    before: ProtocolState,
    after: ProtocolState,
) -> None:
    initiator = dict(config.fields)["initiator"].value
    for node in config.nodes:
        if node == initiator:
            continue
        old_parent = _parent(before, node)
        new_parent = _parent(after, node)
        if old_parent is None and new_parent is not None:
            log.emit("tree_edge", parent=str(new_parent), child=str(node))


def execute_generated_echo(
    config: ProtocolConfig,
    *,
    header: Mapping[str, Any],
    seed: int,
    max_steps: int,
    log_path: Optional[Path],
    scheduler: Scheduler = "random",
    on_event: Optional[EventCallback] = None,
) -> tuple[RunOutcome, EventLog]:
    """Run generated transitions using a protocol-neutral message policy."""

    if not callable(scheduler) and scheduler not in ("random", "fifo", "lifo"):
        raise ValueError(
            "scheduler must be one of: 'random', 'fifo', or 'lifo'"
        )

    log = EventLog(log_path, on_event=on_event)
    log.emit(**header)
    scheduler_random = random.Random(seed)
    previous_state: Optional[ProtocolState] = None
    delivery_steps = 0

    def choose_message(state: ProtocolState) -> int:
        nonlocal delivery_steps
        if callable(scheduler):
            selected_id = scheduler(state.messages)
            if isinstance(selected_id, bool) or not isinstance(selected_id, int):
                raise SchedulerChoiceError(
                    "custom scheduler must return an integer message id"
                )
            selected = [
                message
                for message in state.messages
                if message.identifier == selected_id
            ]
            if not selected:
                raise SchedulerChoiceError(
                    f"custom scheduler selected unqueued message {selected_id}"
                )
            message = selected[0]
        elif scheduler == "random":
            index = scheduler_random.randrange(len(state.messages))
            message = state.messages[index]
        elif scheduler == "fifo":
            message = state.messages[0]
        else:
            message = state.messages[-1]
        delivery_steps += 1
        log.emit(
            "deliver",
            step=delivery_steps,
            message_id=message.identifier,
            kind=_public_message_kind(message.kind),
            sender=str(message.sender),
            receiver=str(message.receiver),
            payload={},
        )
        return message.identifier

    def record_transition(
        state: ProtocolState,
        formal_steps: int,
        event: Optional[ExternalEvent],
    ) -> None:
        nonlocal previous_state
        if event is None:
            previous_state = state
            return

        assert previous_state is not None
        _emit_new_tree_edges(log, config, previous_state, state)
        _emit_new_messages(log, previous_state, state)
        is_start = isinstance(event, StartEvent)
        log.emit(
            "snapshot",
            step=0 if is_start else formal_steps - 1,
            point="after_start" if is_start else "after_delivery",
            **snapshot_from_protocol_state(header, state),
        )
        previous_state = state

    result = generated_echo_executable.run_callback(
        config,
        start_event=generated_echo_executable.start_event(),
        scheduler=choose_message,
        delivery_event=lambda _state, message_id: (
            generated_echo_executable.deliver(message_id)
        ),
        # The public limit counts deliveries. The formal runner also counts
        # its mandatory startup transition.
        max_steps=max_steps + 1,
        observer=record_transition,
    )
    return result, log


__all__ = [
    "EventCallback",
    "MessageSelector",
    "Scheduler",
    "SchedulerChoiceError",
    "SchedulerPolicy",
    "execute_generated_echo",
]
