from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Callable, Dict, Optional, Sequence

from ._version import __version__
from .algorithms import (
    run_bracha_toueg,
    run_dijkstra_scholten,
    run_echo,
    run_lai_yang,
)
from .algorithms.common import AlgorithmResult
from .echo import EchoError, EchoNetwork, run_echo as run_public_echo
from .runtime import RunOutcome
from .topology import load_topology


Runner = Callable[..., AlgorithmResult]
RUNNERS: Dict[str, Runner] = {
    "echo": run_echo,
    "dijkstra-scholten": run_dijkstra_scholten,
    "lai-yang": run_lai_yang,
    "bracha-toueg": run_bracha_toueg,
}


def repository_root() -> Path:
    return Path(__file__).resolve().parent.parent


def default_graph(algorithm: str) -> Path:
    filename = algorithm.replace("-", "_") + ".json"
    return repository_root() / "examples" / filename


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run a distributed algorithm under randomized message delivery."
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"distributed-simulations {__version__}",
    )
    parser.add_argument(
        "algorithm", nargs="?", default="echo", choices=sorted(RUNNERS)
    )
    parser.add_argument("--graph", type=Path)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--max-steps", type=int, default=10_000)
    parser.add_argument(
        "--scheduler",
        choices=("random", "fifo", "lifo"),
        default="random",
        help="Echo queued-message delivery policy (default: random)",
    )
    parser.add_argument(
        "--log",
        type=Path,
        help="write structured JSON Lines events to this path",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        graph_path = args.graph or default_graph(args.algorithm)
        topology = load_topology(graph_path)
        if args.algorithm == "echo":
            result = run_public_echo(
                EchoNetwork.from_topology(topology),
                seed=args.seed,
                max_steps=args.max_steps,
                scheduler=args.scheduler,
                log_path=args.log,
            )
            print(json.dumps(result.to_dict(), indent=2, sort_keys=True))
            return int(not (result.completed and result.verified))

        if args.scheduler != "random":
            parser.error("--scheduler is currently available only for Echo")
        legacy_result = RUNNERS[args.algorithm](
            topology,
            seed=args.seed,
            max_steps=args.max_steps,
            log_path=args.log,
        )
        print(json.dumps(legacy_result.to_dict(), indent=2, sort_keys=True))
        return int(
            not (
                legacy_result.run.outcome == RunOutcome.COMPLETE
                and legacy_result.verified
            )
        )
    except (EchoError, OSError, ValueError) as error:
        parser.exit(2, f"error: {error}\n")
