from __future__ import annotations

import json
import random
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Tuple


@dataclass(frozen=True, order=True)
class RoleId:
    value: str

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True)
class Message:
    message_id: int
    kind: str
    sender_id: RoleId
    receiver_id: RoleId
    payload: Mapping[str, Any] = field(default_factory=dict)


class EventLog:
    def __init__(
        self,
        path: Optional[Path] = None,
        on_event: Optional[Callable[[Mapping[str, Any]], None]] = None,
    ):
        self.path = path
        self.on_event = on_event
        self.events: List[Dict[str, Any]] = []
        if self.path is not None:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            self.path.write_text("", encoding="utf-8")

    def emit(self, event: str, **fields: Any) -> None:
        record = {"event": event, **fields}
        self.events.append(record)
        if self.on_event is not None:
            self.on_event(dict(record))
        if self.path is not None:
            with self.path.open("a", encoding="utf-8") as stream:
                stream.write(json.dumps(record, sort_keys=True) + "\n")


class TaskQueue:
    def __init__(self, seed: int):
        self._random = random.Random(seed)
        self._pending: List[Message] = []

    def enqueue(self, message: Message) -> None:
        self._pending.append(message)

    def dequeue(self) -> Optional[Message]:
        if not self._pending:
            return None
        index = self._random.randrange(len(self._pending))
        return self._pending.pop(index)

    def __len__(self) -> int:
        return len(self._pending)

    @property
    def pending_messages(self) -> Tuple[Message, ...]:
        """Return an immutable scheduler snapshot without changing its order."""

        return tuple(self._pending)


class CommunicationSystem:
    def __init__(self, seed: int, log: EventLog):
        self.queue = TaskQueue(seed)
        self.log = log
        self.roles: Dict[RoleId, Role] = {}
        self._next_message_id = 1

    def register(self, roles: Iterable["Role"]) -> None:
        for role in roles:
            if role.role_id in self.roles:
                raise ValueError(f"duplicate role id: {role.role_id}")
            self.roles[role.role_id] = role

    def send(
        self,
        kind: str,
        sender_id: RoleId,
        receiver_id: RoleId,
        payload: Optional[Mapping[str, Any]] = None,
    ) -> Message:
        if sender_id not in self.roles:
            raise ValueError(f"unknown sender: {sender_id}")
        if receiver_id not in self.roles:
            raise ValueError(f"unknown receiver: {receiver_id}")

        message = Message(
            message_id=self._next_message_id,
            kind=kind,
            sender_id=sender_id,
            receiver_id=receiver_id,
            payload=dict(payload or {}),
        )
        self._next_message_id += 1
        self.queue.enqueue(message)
        self.log.emit(
            "enqueue",
            message_id=message.message_id,
            kind=message.kind,
            sender=str(sender_id),
            receiver=str(receiver_id),
            payload=dict(message.payload),
        )
        return message

    def deliver_next(self, step: int) -> bool:
        message = self.queue.dequeue()
        if message is None:
            return False

        self.log.emit(
            "deliver",
            step=step,
            message_id=message.message_id,
            kind=message.kind,
            sender=str(message.sender_id),
            receiver=str(message.receiver_id),
            payload=dict(message.payload),
        )
        self.roles[message.receiver_id].receive(message)
        return True

    @property
    def pending_count(self) -> int:
        return len(self.queue)

    @property
    def next_message_id(self) -> int:
        """Next envelope identifier, exposed for verified-core adapters."""

        return self._next_message_id

    def snapshot(self) -> Dict[str, Any]:
        """Canonical queue data used by versioned algorithm traces."""

        return {
            "store": [
                {
                    "message_id": message.message_id,
                    "kind": message.kind,
                    "sender": str(message.sender_id),
                    "receiver": str(message.receiver_id),
                    "payload": dict(message.payload),
                }
                for message in self.queue.pending_messages
            ],
            "next_message_id": self._next_message_id,
        }


class Role(ABC):
    def __init__(
        self,
        role_id: RoleId,
        neighbors: Iterable[RoleId],
        communication: CommunicationSystem,
    ):
        self.role_id = role_id
        self.neighbors: Tuple[RoleId, ...] = tuple(neighbors)
        self.communication = communication

    def send(
        self,
        kind: str,
        receiver_id: RoleId,
        payload: Optional[Mapping[str, Any]] = None,
    ) -> Message:
        return self.communication.send(
            kind, self.role_id, receiver_id, payload=payload
        )

    @abstractmethod
    def receive(self, message: Message) -> None:
        raise NotImplementedError

    @abstractmethod
    def is_terminated(self) -> bool:
        raise NotImplementedError


class RunOutcome(str, Enum):
    COMPLETE = "complete"
    STUCK = "stuck"
    BOUNDED = "bounded"


@dataclass(frozen=True)
class RunResult:
    outcome: RunOutcome
    steps: int
    pending_messages: int

    def to_dict(self) -> Dict[str, Any]:
        return {
            "outcome": self.outcome.value,
            "steps": self.steps,
            "pending_messages": self.pending_messages,
        }


class Simulator:
    def __init__(self, seed: int, log_path: Optional[Path] = None):
        self.log = EventLog(log_path)
        self.communication = CommunicationSystem(seed, self.log)

    def register(self, roles: Iterable[Role]) -> None:
        self.communication.register(roles)

    def run(
        self,
        start: Callable[[], None],
        is_complete: Callable[[], bool],
        max_steps: int,
        snapshot: Optional[Callable[[], Mapping[str, Any]]] = None,
    ) -> RunResult:
        if max_steps <= 0:
            raise ValueError("max_steps must be positive")

        start()
        if snapshot is not None:
            self.log.emit("snapshot", step=0, point="after_start", **snapshot())
        steps = 0
        while True:
            pending = self.communication.pending_count
            if is_complete() and pending == 0:
                outcome = RunOutcome.COMPLETE
                break
            if pending == 0:
                outcome = RunOutcome.STUCK
                break
            if steps >= max_steps:
                outcome = RunOutcome.BOUNDED
                break

            self.communication.deliver_next(steps + 1)
            steps += 1
            if snapshot is not None:
                self.log.emit(
                    "snapshot",
                    step=steps,
                    point="after_delivery",
                    **snapshot(),
                )

        result = RunResult(outcome, steps, self.communication.pending_count)
        self.log.emit("run_finished", **result.to_dict())
        return result
