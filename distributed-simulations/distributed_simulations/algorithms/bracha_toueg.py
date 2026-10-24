from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Mapping, Optional, Set

from ..runtime import RoleId, RunOutcome, Simulator
from ..topology import Topology
from .common import AlgorithmResult
from .lai_yang import (
    SnapshotRole,
    create_snapshot_roles,
    snapshot_details,
    start_snapshot_run,
)


def detect_deadlocked_roles(
    roles: Mapping[RoleId, SnapshotRole]
) -> Set[RoleId]:
    wait_for = {
        role_id: set(role.snapshot.outgoing_requests)
        for role_id, role in roles.items()
        if role.snapshot is not None
    }

    index = 0
    stack: List[RoleId] = []
    on_stack: Set[RoleId] = set()
    indices: Dict[RoleId, int] = {}
    low_links: Dict[RoleId, int] = {}
    deadlocked: Set[RoleId] = set()

    def visit(node: RoleId) -> None:
        nonlocal index
        indices[node] = index
        low_links[node] = index
        index += 1
        stack.append(node)
        on_stack.add(node)

        for target in wait_for.get(node, set()):
            if target not in indices:
                visit(target)
                low_links[node] = min(low_links[node], low_links[target])
            elif target in on_stack:
                low_links[node] = min(low_links[node], indices[target])

        if low_links[node] != indices[node]:
            return
        component: Set[RoleId] = set()
        while True:
            member = stack.pop()
            on_stack.remove(member)
            component.add(member)
            if member == node:
                break
        if len(component) > 1 or node in wait_for.get(node, set()):
            deadlocked.update(component)

    for role_id in wait_for:
        if role_id not in indices:
            visit(role_id)
    return deadlocked


def run_bracha_toueg(
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
    deadlocked = detect_deadlocked_roles(roles)
    verified = run.outcome == RunOutcome.COMPLETE and all(
        role.snapshot is not None for role in roles.values()
    )
    details = {
        "deadlocked_roles": sorted(str(role_id) for role_id in deadlocked),
        "snapshots": snapshot_details(roles),
    }
    return AlgorithmResult("bracha-toueg", run, verified, details)
