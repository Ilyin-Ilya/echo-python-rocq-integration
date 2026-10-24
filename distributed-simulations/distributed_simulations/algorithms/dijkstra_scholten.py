from __future__ import annotations

from pathlib import Path
from typing import Dict, Iterable, Optional, Set

from ..runtime import Message, Role, RoleId, RunOutcome, Simulator
from ..topology import Topology, initiator_id, neighbors
from .common import AlgorithmResult


WORK = "WORK"
RETURN = "RETURN"


class TerminationInitiator(Role):
    def __init__(self, role_id: RoleId, neighbor_ids: Iterable[RoleId], communication):
        super().__init__(role_id, neighbor_ids, communication)
        self.pending: Set[RoleId] = set()
        self.started = False

    @property
    def ref_count(self) -> int:
        return len(self.pending)

    def start(self) -> None:
        self.started = True
        self.pending = set(self.neighbors)
        for neighbor_id in self.neighbors:
            self.send(WORK, neighbor_id)

    def receive(self, message: Message) -> None:
        if message.kind == WORK:
            self.send(RETURN, message.sender_id)
            return
        if message.kind != RETURN:
            raise ValueError(f"unexpected termination message: {message.kind}")
        if message.sender_id not in self.pending:
            raise ValueError(f"unexpected RETURN from {message.sender_id}")
        self.pending.remove(message.sender_id)

    def is_terminated(self) -> bool:
        return self.started and not self.pending


class TerminationParticipant(Role):
    def __init__(self, role_id: RoleId, neighbor_ids: Iterable[RoleId], communication):
        super().__init__(role_id, neighbor_ids, communication)
        self.parent: Optional[RoleId] = None
        self.pending: Set[RoleId] = set()
        self.engaged = False
        self.returned = False

    @property
    def ref_count(self) -> int:
        return len(self.pending)

    def receive(self, message: Message) -> None:
        if message.kind == WORK:
            self._receive_work(message.sender_id)
            return
        if message.kind == RETURN:
            self._receive_return(message.sender_id)
            return
        raise ValueError(f"unexpected termination message: {message.kind}")

    def _receive_work(self, sender_id: RoleId) -> None:
        if self.engaged or self.returned:
            self.send(RETURN, sender_id)
            return

        self.engaged = True
        self.parent = sender_id
        self.pending = set(self.neighbors) - {sender_id}
        for neighbor_id in self.pending:
            self.send(WORK, neighbor_id)
        self._return_if_ready()

    def _receive_return(self, sender_id: RoleId) -> None:
        if sender_id not in self.pending:
            raise ValueError(f"unexpected RETURN from {sender_id}")
        self.pending.remove(sender_id)
        self._return_if_ready()

    def _return_if_ready(self) -> None:
        if not self.engaged or self.pending or self.returned or self.parent is None:
            return
        self.returned = True
        self.send(RETURN, self.parent)

    def is_terminated(self) -> bool:
        return self.returned


def run_dijkstra_scholten(
    topology: Topology,
    *,
    seed: int = 0,
    max_steps: int = 10_000,
    log_path: Optional[Path] = None,
) -> AlgorithmResult:
    root_id = initiator_id(topology)
    simulator = Simulator(seed, log_path)
    roles: Dict[RoleId, Role] = {}

    for node_id in topology:
        role_id = RoleId(node_id)
        role_neighbors = neighbors(topology, role_id)
        if role_id == root_id:
            role = TerminationInitiator(
                role_id, role_neighbors, simulator.communication
            )
        else:
            role = TerminationParticipant(
                role_id, role_neighbors, simulator.communication
            )
        roles[role_id] = role

    simulator.register(roles.values())
    root = roles[root_id]
    assert isinstance(root, TerminationInitiator)
    run = simulator.run(
        root.start,
        lambda: all(role.is_terminated() for role in roles.values()),
        max_steps,
    )
    counters = {
        str(role_id): role.ref_count
        for role_id, role in roles.items()
        if isinstance(role, (TerminationInitiator, TerminationParticipant))
    }
    verified = (
        run.outcome == RunOutcome.COMPLETE
        and all(role.is_terminated() for role in roles.values())
        and all(value == 0 for value in counters.values())
    )
    return AlgorithmResult(
        "dijkstra-scholten", run, verified, {"ref_counts": counters}
    )
