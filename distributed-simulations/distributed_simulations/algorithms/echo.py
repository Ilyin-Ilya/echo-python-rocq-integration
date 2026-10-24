from __future__ import annotations

from pathlib import Path
from typing import Dict, Optional, Set

from ..protocol_values import (
    ProtocolConfig,
    ProtocolState,
    RunOutcome as IRRunOutcome,
    RunStatus as IRRunStatus,
)
from ..runtime import RoleId, RunOutcome, RunResult
from ..topology import Topology, initiator_id, validate_topology
from .common import AlgorithmResult
from . import generated_echo_executable
from .echo_codec import config_from_topology
from .echo_execution import EventCallback, Scheduler, execute_generated_echo


def run_echo(
    topology: Topology,
    *,
    seed: int = 0,
    max_steps: int = 10_000,
    log_path: Optional[Path] = None,
    scheduler: Scheduler = "random",
    capture_trace: bool = False,
    on_event: Optional[EventCallback] = None,
) -> AlgorithmResult:
    """Run Echo through Python functions generated from the Rocq IR program."""

    from .echo_trace import trace_header

    validate_topology(topology)
    if max_steps <= 0:
        raise ValueError("max_steps must be positive")

    root_id = initiator_id(topology)
    config = config_from_topology(topology, root_id)
    header = trace_header(topology, root_id, seed, max_steps)
    header["scheduler"] = scheduler
    result, log = execute_generated_echo(
        config,
        header=header,
        seed=seed,
        max_steps=max_steps,
        log_path=log_path,
        scheduler=scheduler,
        on_event=on_event,
    )
    run_result = _runtime_result(result)
    log.emit("run_finished", **run_result.to_dict())

    verified = run_result.outcome == RunOutcome.COMPLETE and _validate_parent_tree(
        config, result.state
    )
    parents: Dict[str, str] = {
        str(node): str(parent)
        for node in config.nodes
        if node != root_id
        for parent in (_parent(result.state, node),)
        if parent is not None
    }
    return AlgorithmResult(
        "echo",
        run_result,
        verified,
        {
            "parents": parents,
            "canonical_runner_proof_covered": True,
            "verification_scope": "runtime-check-and-canonical-runner-proof",
        },
        tuple(log.events) if capture_trace else (),
    )


def _parent(state: ProtocolState, node: RoleId) -> Optional[RoleId]:
    return dict(state.local_fields(node))["parent"].value


def _validate_parent_tree(config: ProtocolConfig, state: ProtocolState) -> bool:
    """Independently check the completed parent tree returned by the protocol."""

    if generated_echo_executable.is_complete(config, state) is not True:
        return False

    initiator = dict(config.fields)["initiator"].value
    parents = {
        node: _parent(state, node)
        for node in config.nodes
        if node != initiator
    }
    for child, parent in parents.items():
        if parent is None or parent not in config.neighbors_of(child):
            return False

        seen: Set[RoleId] = set()
        current = child
        while current != initiator:
            if current in seen or current not in parents:
                return False
            seen.add(current)
            next_parent = parents[current]
            if next_parent is None:
                return False
            current = next_parent
    return True


def _runtime_result(result: IRRunOutcome) -> RunResult:
    outcome_map = {
        IRRunStatus.COMPLETE: RunOutcome.COMPLETE,
        IRRunStatus.STUCK: RunOutcome.STUCK,
        IRRunStatus.BOUNDED: RunOutcome.BOUNDED,
    }
    if result.status not in outcome_map:
        detail = f": {result.error}" if result.error else ""
        raise RuntimeError(
            f"generated Echo runner rejected its scheduler choice: "
            f"{result.status.value}{detail}"
        )
    # The formal runner counts startup as a transition. The public Python
    # result historically counts only delivered messages, so retain that API.
    delivery_steps = max(result.steps - 1, 0)
    return RunResult(
        outcome_map[result.status], delivery_steps, len(result.state.messages)
    )
