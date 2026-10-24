"""Deterministic topology generators used by Echo exploration."""

from __future__ import annotations

from typing import Dict, Iterable, List, Set

from ..topology import Topology


def _topology(adjacency: Dict[str, Set[str]], root: str = "A") -> Topology:
    return {
        node: {
            "role": "initiator" if node == root else "participant",
            "neighbors": sorted(neighbors),
        }
        for node, neighbors in sorted(adjacency.items())
    }


def _nodes(size: int) -> List[str]:
    if size <= 0:
        raise ValueError("topology size must be positive")
    if size > 26:
        raise ValueError("topology generators support at most 26 nodes")
    return [chr(ord("A") + index) for index in range(size)]


def line_topology(size: int) -> Topology:
    nodes = _nodes(size)
    adjacency = {node: set() for node in nodes}
    for left, right in zip(nodes, nodes[1:]):
        adjacency[left].add(right)
        adjacency[right].add(left)
    return _topology(adjacency)


def ring_topology(size: int) -> Topology:
    if size < 3:
        raise ValueError("ring topology requires at least three nodes")
    nodes = _nodes(size)
    adjacency = {node: set() for node in nodes}
    for index, node in enumerate(nodes):
        neighbor = nodes[(index + 1) % size]
        adjacency[node].add(neighbor)
        adjacency[neighbor].add(node)
    return _topology(adjacency)


def binary_tree_topology(size: int) -> Topology:
    nodes = _nodes(size)
    adjacency = {node: set() for node in nodes}
    for child_index in range(1, size):
        parent_index = (child_index - 1) // 2
        parent, child = nodes[parent_index], nodes[child_index]
        adjacency[parent].add(child)
        adjacency[child].add(parent)
    return _topology(adjacency)


def dense_topology(size: int) -> Topology:
    nodes = _nodes(size)
    return _topology({node: set(nodes) - {node} for node in nodes})
