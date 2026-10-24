from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Mapping, Set

from .runtime import RoleId


Topology = Dict[str, Dict[str, Any]]


def load_topology(path: Path) -> Topology:
    with path.open(encoding="utf-8") as stream:
        data = json.load(stream)
    if not isinstance(data, dict):
        raise ValueError("topology must be a JSON object")
    validate_topology(data)
    return data


def validate_topology(
    topology: Mapping[str, Mapping[str, Any]],
    *,
    require_connected: bool = True,
    require_undirected: bool = True,
) -> None:
    if not topology:
        raise ValueError("topology must contain at least one role")

    node_ids = set(topology)
    adjacency: Dict[str, Set[str]] = {}
    for node_id, node in topology.items():
        if not isinstance(node_id, str) or not node_id:
            raise ValueError("role ids must be non-empty strings")
        if not isinstance(node, Mapping):
            raise ValueError(f"configuration for {node_id} must be a JSON object")
        neighbors = node.get("neighbors", [])
        if not isinstance(neighbors, list) or not all(
            isinstance(neighbor, str) for neighbor in neighbors
        ):
            raise ValueError(f"neighbors for {node_id} must be a string list")
        if len(neighbors) != len(set(neighbors)):
            raise ValueError(f"duplicate neighbor for {node_id}")
        if node_id in neighbors:
            raise ValueError(f"self edge for {node_id}")
        unknown = set(neighbors) - node_ids
        if unknown:
            raise ValueError(
                f"unknown neighbors for {node_id}: {', '.join(sorted(unknown))}"
            )

        requests = node.get("requests", [])
        if not isinstance(requests, list) or not all(
            isinstance(request, str) for request in requests
        ):
            raise ValueError(f"requests for {node_id} must be a string list")
        if len(requests) != len(set(requests)):
            raise ValueError(f"duplicate request for {node_id}")
        unknown_requests = set(requests) - node_ids
        if unknown_requests:
            raise ValueError(
                f"unknown requests for {node_id}: "
                f"{', '.join(sorted(unknown_requests))}"
            )
        non_neighbor_requests = set(requests) - set(neighbors)
        if non_neighbor_requests:
            raise ValueError(
                f"non-neighbor requests for {node_id}: "
                f"{', '.join(sorted(non_neighbor_requests))}"
            )
        adjacency[node_id] = set(neighbors)

    if require_undirected:
        for node_id, neighbors in adjacency.items():
            for neighbor in neighbors:
                if node_id not in adjacency[neighbor]:
                    raise ValueError(
                        f"edge {node_id}-{neighbor} is not symmetric"
                    )

    if require_connected:
        start = next(iter(node_ids))
        visited: Set[str] = set()
        stack = [start]
        while stack:
            node_id = stack.pop()
            if node_id in visited:
                continue
            visited.add(node_id)
            stack.extend(adjacency[node_id] - visited)
        if visited != node_ids:
            missing = ", ".join(sorted(node_ids - visited))
            raise ValueError(f"topology is disconnected: {missing}")


def initiator_id(topology: Mapping[str, Mapping[str, Any]]) -> RoleId:
    initiators = [
        RoleId(node_id)
        for node_id, node in topology.items()
        if node.get("role") == "initiator"
    ]
    if len(initiators) != 1:
        raise ValueError("topology must define exactly one initiator")
    return initiators[0]


def neighbors(
    topology: Mapping[str, Mapping[str, Any]], node_id: RoleId
) -> List[RoleId]:
    return [RoleId(value) for value in topology[node_id.value].get("neighbors", [])]
