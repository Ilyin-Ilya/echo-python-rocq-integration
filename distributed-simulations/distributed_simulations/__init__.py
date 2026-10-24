"""Single-process emulation of message-passing distributed algorithms."""

from ._version import __version__
from .echo import EchoNetwork, EchoResult, run_echo
from .runtime import RunOutcome, RunResult

__all__ = [
    "EchoNetwork",
    "EchoResult",
    "RunOutcome",
    "RunResult",
    "__version__",
    "run_echo",
]
