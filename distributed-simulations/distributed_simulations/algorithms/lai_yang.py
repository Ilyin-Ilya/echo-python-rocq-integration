from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, Mapping, Optional, Set

from ..runtime import Message, Role, RoleId, RunOutcome, Simulator
from ..topology import Topology, initiator_id, neighbors
from .common import AlgorithmResult


REQUEST = "REQUEST"
GRANT = "GRANT"
SNAPSHOT = "SNAPSHOT"


@dataclass(frozen=True)
class SnapshotRecord:
    incoming_requests: FrozenSet[RoleId]
    outgoing_requests: FrozenSet[RoleId]


class SnapshotRole(Role):
    def __init__(
        self,
        role_id: RoleId,
        neighbor_ids: Iterable[RoleId],
        communication,
        requests: Iterable[RoleId],
    ):
        super().__init__(role_id, neighbor_ids, communication)
        self.configured_requests = tuple(requests)
        self.incoming_requests: Set[RoleId] = set()
        self.outgoing_requests: Set[RoleId] = set()
        self.snapshot_sequence: Optional[int] = None
        self.snapshot: Optional[SnapshotRecord] = None

    def start_requests(self) -> None:
        for target in self.configured_requests:
            if target not in self.neighbors:
                raise ValueError(f"{self.role_id} cannot request non-neighbor {target}")
            self.outgoing_requests.add(target)
            self.send(REQUEST, target)

    def take_snapshot(self, sequence: int) -> None:
        if self.snapshot_sequence == sequence:
            return
        if self.snapshot_sequence is not None:
            raise ValueError("only one snapshot is supported per run")

        self.snapshot_sequence = sequence
        self.snapshot = SnapshotRecord(
            incoming_requests=frozenset(self.incoming_requests),
            outgoing_requests=frozenset(self.outgoing_requests),
        )
        self.communication.log.emit(
            "snapshot",
            role=str(self.role_id),
            sequence=sequence,
            incoming=sorted(str(value) for value in self.incoming_requests),
            outgoing=sorted(str(value) for value in self.outgoing_requests),
        )
        for neighbor_id in self.neighbors:
            self.send(SNAPSHOT, neighbor_id, {"sequence": sequence})

    def receive(self, message: Message) -> None:
        if message.kind == REQUEST:
            self.incoming_requests.add(message.sender_id)
            return
        if message.kind == GRANT:
            self.outgoing_requests.discard(message.sender_id)
            return
        if message.kind == SNAPSHOT:
            self.take_snapshot(int(message.payload["sequence"]))
            return
        raise ValueError(f"unexpected snapshot message: {message.kind}")

    def is_terminated(self) -> bool:
        return self.snapshot is not None


def create_snapshot_roles(topology: Topology, simulator: Simulator):
    roles: Dict[RoleId, SnapshotRole] = {}
    for node_id, node in topology.items():
        role_id = RoleId(node_id)
        configured_requests = [RoleId(value) for value in node.get("requests", [])]
        roles[role_id] = SnapshotRole(
            role_id,
            neighbors(topology, role_id),
            simulator.communication,
            configured_requests,
        )
    simulator.register(roles.values())
    return roles


def start_snapshot_run(
    topology: Topology,
    roles: Mapping[RoleId, SnapshotRole],
) -> None:
    for role in roles.values():
        role.start_requests()
    roles[initiator_id(topology)].take_snapshot(1)


def snapshot_details(roles: Mapping[RoleId, SnapshotRole]):
    return {
        str(role_id): {
            "incoming": sorted(str(value) for value in role.snapshot.incoming_requests),
            "outgoing": sorted(str(value) for value in role.snapshot.outgoing_requests),
        }
        for role_id, role in roles.items()
        if role.snapshot is not None
    }


def run_lai_yang(
    topology: Topology,
    *,
    seed: int = 0,
    max_steps: int = 10_000,
    log_path: Optional[Path] = None,
) -> AlgorithmResult:
    simulator = Simulator(seed, log_path)
    roles = create_snapshot_roles(topology, simulator)
    run = simulator.run(
        lambda: start_snapshot_run(topology, roles),
        lambda: all(role.is_terminated() for role in roles.values()),
        max_steps,
    )
    verified = run.outcome == RunOutcome.COMPLETE and all(
        role.snapshot is not None for role in roles.values()
    )
    return AlgorithmResult(
        "lai-yang", run, verified, {"snapshots": snapshot_details(roles)}
    )
