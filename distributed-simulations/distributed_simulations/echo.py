"""Friendly public Python API for the Rocq-generated Echo protocol."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import (
    Any,
    Callable,
    Iterable,
    Mapping,
    Optional,
    Sequence,
    Tuple,
    Union,
    cast,
)

from .algorithms.echo import run_echo as _run_echo
from .algorithms.echo_execution import (
    EventCallback,
    SchedulerChoiceError,
    SchedulerPolicy,
)
from .runtime import RunOutcome
from .topology import Topology, initiator_id, load_topology, validate_topology


class EchoError(Exception):
    """Base class for errors raised by the public Echo API."""


class InvalidTopologyError(EchoError, ValueError):
    """The supplied network is not a valid Echo topology."""


class InvalidRunConfigurationError(EchoError, ValueError):
    """A scheduler or execution-bound option is invalid."""


class EchoExecutionError(EchoError, RuntimeError):
    """The generated transition runner rejected an execution."""


@dataclass(frozen=True)
class PendingMessage:
    """Read-only queued-message information exposed to custom schedulers."""

    message_id: int
    kind: str
    sender: str
    receiver: str


MessageScheduler = Callable[[Tuple[PendingMessage, ...]], int]
PublicScheduler = Union[SchedulerPolicy, MessageScheduler]


@dataclass(frozen=True)
class EchoNetwork:
    """Validated undirected network and its distinguished initiator."""

    adjacency: Mapping[str, Sequence[str]]
    initiator: str

    def __post_init__(self) -> None:
        if not isinstance(self.initiator, str) or not self.initiator:
            raise InvalidTopologyError("initiator must be a non-empty string")

        normalized = {}
        for node, neighbors in self.adjacency.items():
            if not isinstance(node, str) or not node:
                raise InvalidTopologyError("node ids must be non-empty strings")
            if isinstance(neighbors, (str, bytes)):
                raise InvalidTopologyError(
                    f"neighbors for {node!r} must be a sequence of node ids"
                )
            normalized[node] = tuple(neighbors)

        object.__setattr__(self, "adjacency", MappingProxyType(normalized))
        try:
            validate_topology(self.to_topology())
        except ValueError as error:
            raise InvalidTopologyError(str(error)) from error

    @classmethod
    def from_adjacency(
        cls,
        adjacency: Mapping[str, Sequence[str]],
        *,
        initiator: str,
    ) -> "EchoNetwork":
        """Construct a network from a symmetric adjacency mapping."""

        return cls(adjacency, initiator)

    @classmethod
    def from_edges(
        cls,
        edges: Iterable[Tuple[str, str]],
        *,
        initiator: str,
        nodes: Iterable[str] = (),
    ) -> "EchoNetwork":
        """Construct a network from undirected edges and optional isolated nodes."""

        adjacency = {node: [] for node in nodes}
        adjacency.setdefault(initiator, [])
        for edge in edges:
            if isinstance(edge, (str, bytes)):
                raise InvalidTopologyError(
                    "each edge must contain exactly two node ids"
                )
            try:
                left, right = edge
            except (TypeError, ValueError) as error:
                raise InvalidTopologyError(
                    "each edge must contain exactly two node ids"
                ) from error
            adjacency.setdefault(left, []).append(right)
            adjacency.setdefault(right, []).append(left)
        return cls(adjacency, initiator)

    @classmethod
    def from_topology(cls, topology: Mapping[str, Mapping[str, Any]]) -> "EchoNetwork":
        """Construct from the repository's legacy JSON topology shape."""

        try:
            validate_topology(topology)
            root = str(initiator_id(topology))
        except ValueError as error:
            raise InvalidTopologyError(str(error)) from error
        return cls(
            {
                node: tuple(config.get("neighbors", ()))
                for node, config in topology.items()
            },
            root,
        )

    @classmethod
    def from_json(cls, path: Union[str, Path]) -> "EchoNetwork":
        """Load the existing versioned topology JSON representation."""

        try:
            return cls.from_topology(load_topology(Path(path)))
        except (OSError, ValueError) as error:
            if isinstance(error, InvalidTopologyError):
                raise
            raise InvalidTopologyError(str(error)) from error

    def to_topology(self) -> Topology:
        """Return the internal topology representation used by the adapter."""

        return {
            node: {
                "role": "initiator" if node == self.initiator else "participant",
                "neighbors": list(neighbors),
            }
            for node, neighbors in self.adjacency.items()
        }

    @property
    def nodes(self) -> Tuple[str, ...]:
        """Node identifiers in stable input order."""

        return tuple(self.adjacency)

    @property
    def edges(self) -> Tuple[Tuple[str, str], ...]:
        """Undirected edges, each returned exactly once."""

        seen = set()
        edges = []
        for left, neighbors in self.adjacency.items():
            for right in neighbors:
                key = frozenset((left, right))
                if key in seen:
                    continue
                seen.add(key)
                edges.append((left, right))
        return tuple(edges)

    def neighbors_of(self, node: str) -> Tuple[str, ...]:
        """Return a node's neighbors without exposing mutable topology state."""

        try:
            return tuple(self.adjacency[node])
        except KeyError as error:
            raise KeyError(f"unknown Echo node {node!r}") from error


@dataclass(frozen=True)
class EchoVerification:
    """What the returned ``verified`` flag is backed by."""

    canonical_runner_proof_covered: bool
    scope: str

    @property
    def explanation(self) -> str:
        """Human-readable meaning of the verification metadata."""

        if self.canonical_runner_proof_covered:
            return (
                "The completed runtime tree was checked in Python and the "
                "canonical generated runner is covered by the Rocq "
                "complete-run spanning-tree theorem."
            )
        return "The result is not covered by the canonical runner theorem."


@dataclass(frozen=True)
class EchoResult:
    """Typed result returned by :func:`run_echo`."""

    outcome: RunOutcome
    steps: int
    pending_messages: int
    verified: bool
    initiator: str
    nodes: Tuple[str, ...]
    parents: Mapping[str, str]
    verification: EchoVerification
    trace: Tuple[Mapping[str, Any], ...] = ()

    @property
    def completed(self) -> bool:
        """Whether execution reached the generated completion predicate."""

        return self.outcome is RunOutcome.COMPLETE

    @property
    def tree_edges(self) -> Tuple[Tuple[str, str], ...]:
        """Return completed tree edges as ``(parent, child)`` pairs."""

        return tuple(
            (self.parents[node], node)
            for node in self.nodes
            if node in self.parents
        )

    def parent_of(self, node: str) -> Optional[str]:
        """Return a node's parent, or ``None`` for the root or undiscovered node."""

        if node not in self.nodes:
            raise KeyError(f"unknown Echo node {node!r}")
        return self.parents.get(node)

    def children_of(self, node: str) -> Tuple[str, ...]:
        """Return children in stable network order."""

        if node not in self.nodes:
            raise KeyError(f"unknown Echo node {node!r}")
        return tuple(
            child for child in self.nodes if self.parents.get(child) == node
        )

    def path_to_initiator(self, node: str) -> Optional[Tuple[str, ...]]:
        """Return ``node ... initiator``, or ``None`` for an incomplete path."""

        if node not in self.nodes:
            raise KeyError(f"unknown Echo node {node!r}")
        path = [node]
        seen = set()
        while path[-1] != self.initiator:
            current = path[-1]
            if current in seen:
                return None
            seen.add(current)
            parent = self.parents.get(current)
            if parent is None:
                return None
            path.append(parent)
        return tuple(path)

    def to_dict(self) -> Mapping[str, Any]:
        """Return a JSON-compatible representation."""

        result = {
            "algorithm": "echo",
            "outcome": self.outcome.value,
            "steps": self.steps,
            "pending_messages": self.pending_messages,
            "verified": self.verified,
            "initiator": self.initiator,
            "nodes": list(self.nodes),
            "parents": dict(self.parents),
            "verification": {
                "canonical_runner_proof_covered": (
                    self.verification.canonical_runner_proof_covered
                ),
                "scope": self.verification.scope,
            },
        }
        if self.trace:
            result["trace"] = [dict(event) for event in self.trace]
        return result


Adjacency = Mapping[str, Sequence[str]]
LegacyTopology = Mapping[str, Mapping[str, Any]]
NetworkInput = Union[EchoNetwork, Adjacency, LegacyTopology]


def run_echo(
    network: NetworkInput,
    *,
    initiator: Optional[str] = None,
    seed: int = 0,
    max_steps: int = 10_000,
    scheduler: PublicScheduler = "random",
    log_path: Optional[Path] = None,
    capture_trace: bool = False,
    on_event: Optional[EventCallback] = None,
) -> EchoResult:
    """Run the generated Echo implementation through a stable Python API."""

    if max_steps <= 0:
        raise InvalidRunConfigurationError("max_steps must be positive")
    if not callable(scheduler) and scheduler not in ("random", "fifo", "lifo"):
        raise InvalidRunConfigurationError(
            "scheduler must be one of: 'random', 'fifo', or 'lifo'"
        )

    if isinstance(network, EchoNetwork):
        if initiator is not None and initiator != network.initiator:
            raise InvalidTopologyError(
                "initiator does not match the supplied EchoNetwork"
            )
        echo_network = network
    elif initiator is not None:
        echo_network = EchoNetwork.from_adjacency(
            cast(Adjacency, network), initiator=initiator
        )
    else:
        echo_network = EchoNetwork.from_topology(cast(LegacyTopology, network))
    adapted_scheduler = scheduler
    if callable(scheduler):
        user_scheduler = scheduler

        def select_message(messages):
            return user_scheduler(
                tuple(
                    PendingMessage(
                        message.identifier,
                        message.kind,
                        str(message.sender),
                        str(message.receiver),
                    )
                    for message in messages
                )
            )

        adapted_scheduler = select_message

    try:
        internal = _run_echo(
            echo_network.to_topology(),
            seed=seed,
            max_steps=max_steps,
            log_path=log_path,
            scheduler=adapted_scheduler,
            capture_trace=capture_trace,
            on_event=on_event,
        )
    except SchedulerChoiceError as error:
        raise InvalidRunConfigurationError(str(error)) from error
    except InvalidRunConfigurationError:
        raise
    except RuntimeError as error:
        raise EchoExecutionError(str(error)) from error

    parents = internal.details.get("parents")
    if not isinstance(parents, Mapping):
        raise EchoExecutionError("Echo runner returned invalid parent data")
    proof_covered = internal.details.get("canonical_runner_proof_covered")
    scope = internal.details.get("verification_scope")
    if not isinstance(proof_covered, bool) or not isinstance(scope, str):
        raise EchoExecutionError("Echo runner returned invalid verification metadata")

    return EchoResult(
        outcome=internal.run.outcome,
        steps=internal.run.steps,
        pending_messages=internal.run.pending_messages,
        verified=internal.verified,
        initiator=echo_network.initiator,
        nodes=echo_network.nodes,
        parents=MappingProxyType(dict(parents)),
        verification=EchoVerification(proof_covered, scope),
        trace=tuple(dict(event) for event in internal.events),
    )


__all__ = [
    "EchoError",
    "EchoExecutionError",
    "EchoNetwork",
    "EchoResult",
    "EchoVerification",
    "InvalidRunConfigurationError",
    "InvalidTopologyError",
    "MessageScheduler",
    "PendingMessage",
    "RunOutcome",
    "run_echo",
]
