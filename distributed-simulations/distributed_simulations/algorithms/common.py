from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Mapping, Tuple

from ..runtime import RunResult


@dataclass(frozen=True)
class AlgorithmResult:
    algorithm: str
    run: RunResult
    verified: bool
    details: Mapping[str, Any] = field(default_factory=dict)
    events: Tuple[Mapping[str, Any], ...] = field(
        default_factory=tuple, repr=False, compare=False
    )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "algorithm": self.algorithm,
            **self.run.to_dict(),
            "verified": self.verified,
            "details": dict(self.details),
        }
