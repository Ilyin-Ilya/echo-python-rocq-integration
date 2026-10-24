"""Protocol-neutral support for generating executable artifacts from Rocq.

Protocol generators provide their compiled export modules, source dependencies,
Rocq expressions, schema validation, and renderer. This module owns only the
reusable transport boundary: locating Rocq, rejecting stale compiled exports,
evaluating string exports, parsing the interchange format, and replacing
generated files atomically.
"""

from __future__ import annotations

import os
import hashlib
import pprint
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


MACOS_ROCQ_ROOT = Path(
    "/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources"
)


class GenerationError(RuntimeError):
    """A Rocq export could not be evaluated, decoded, or generated safely."""


RocqReplCommand = tuple[str, ...]


@dataclass(frozen=True)
class RocqStringExport:
    """One compiled Rocq string expression and the sources it depends on."""

    expression: str
    compiled_module: Path
    sources: tuple[Path, ...]


@dataclass(frozen=True)
class ProtocolExportDescriptor:
    """The formal export boundary for one generic protocol IR program."""

    protocol_id: str
    schema_version: int
    ir_version: int
    logical_root: str
    imports: tuple[str, ...]
    export: RocqStringExport


@dataclass(frozen=True)
class ProtocolEnvelope:
    """A validated, versioned protocol IR value evaluated by Rocq."""

    protocol_id: str
    schema_version: int
    ir_version: int
    signature: tuple
    program: tuple
    raw: tuple


def find_coqtop(explicit: str | None) -> RocqReplCommand:
    """Find either the legacy ``coqtop`` executable or ``rocq repl``."""

    if explicit:
        candidate = Path(explicit)
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return (str(candidate.resolve()),)
        raise GenerationError(f"configured coqtop is not executable: {candidate}")

    coqbin = os.environ.get("COQBIN")
    if coqbin:
        directory = Path(coqbin)
        for name, suffix in (("coqtop", ()), ("rocq", ("repl",))):
            candidate = directory / name
            if candidate.is_file() and os.access(candidate, os.X_OK):
                return (str(candidate.resolve()), *suffix)

    for name, suffix in (("coqtop", ()), ("rocq", ("repl",))):
        on_path = shutil.which(name)
        if on_path:
            return (str(Path(on_path).resolve()), *suffix)

    for name, suffix in (("coqtop", ()), ("rocq", ("repl",))):
        candidate = MACOS_ROCQ_ROOT / "bin" / name
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return (str(candidate.resolve()), *suffix)

    raise GenerationError(
        "neither coqtop nor rocq repl was found; pass --coqtop or set COQBIN "
        "to the Rocq bin directory"
    )


def find_rocqlib(explicit: str | None) -> Path | None:
    if explicit:
        return Path(explicit).resolve()
    configured = os.environ.get("ROCQLIB")
    if configured:
        return Path(configured).resolve()
    bundled = MACOS_ROCQ_ROOT / "lib" / "coq"
    return bundled.resolve() if bundled.is_dir() else None


def evaluate_string_exports(
    *,
    rocq_project: Path,
    theories: Path,
    logical_root: str,
    imports: Sequence[str],
    exports: Sequence[RocqStringExport],
    coqtop: RocqReplCommand,
    rocqlib: Path | None,
    description: str,
) -> tuple[str, ...]:
    """Evaluate string exports from any Rocq protocol project."""

    stale_sources: list[Path] = []
    for export in exports:
        if not export.compiled_module.is_file():
            raise GenerationError(
                f"{export.compiled_module} is missing; build {description} before generation"
            )
        for source in export.sources:
            if not source.is_file():
                raise GenerationError(f"Rocq export source is missing: {source}")
            if source.stat().st_mtime_ns > export.compiled_module.stat().st_mtime_ns:
                stale_sources.append(source)
    if stale_sources:
        rendered = ", ".join(str(source) for source in stale_sources)
        raise GenerationError(
            "compiled Rocq export is older than its source; rebuild before generation: "
            + rendered
        )

    commands = "\n".join(
        (
            "From Stdlib Require Import String.",
            f"From {logical_root} Require Import {' '.join(imports)}.",
            "Open Scope string_scope.",
            "Set Printing Width 1000000.",
            *(f"Eval vm_compute in {export.expression}." for export in exports),
            "",
        )
    )
    environment = os.environ.copy()
    if rocqlib is not None:
        environment["ROCQLIB"] = str(rocqlib)
    result = subprocess.run(
        [
            *coqtop,
            "-quiet",
            "-R",
            str(theories.resolve()),
            logical_root,
        ],
        input=commands,
        text=True,
        capture_output=True,
        cwd=rocq_project,
        env=environment,
        check=False,
    )
    if result.returncode != 0:
        raise GenerationError(
            f"Rocq failed to evaluate {description} generation exports:\n"
            + result.stderr.strip()
        )
    matches = re.findall(r'= "([^"\\]*)"\s*\n\s*: string', result.stdout)
    if len(matches) != len(exports):
        raise GenerationError(
            f"expected {len(exports)} evaluated strings in coqtop output, "
            f"found {len(matches)}:\n{result.stdout.strip()}"
        )
    return tuple(matches)


def parse_sexpr(source: str) -> tuple:
    """Parse the deliberately small, string-free S-expression interchange."""

    tokens = re.findall(r"\(|\)|[^\s()]+", source)
    position = 0

    def parse_one():
        nonlocal position
        if position >= len(tokens):
            raise GenerationError("unexpected end of S-expression")
        token = tokens[position]
        position += 1
        if token == "(":
            values = []
            while True:
                if position >= len(tokens):
                    raise GenerationError("unclosed S-expression")
                if tokens[position] == ")":
                    position += 1
                    return tuple(values)
                values.append(parse_one())
        if token == ")":
            raise GenerationError("unexpected ')' in S-expression")
        return token

    parsed = parse_one()
    if position != len(tokens):
        raise GenerationError("trailing tokens after S-expression")
    if not isinstance(parsed, tuple):
        raise GenerationError("the exported value must be a list")
    return parsed


def _single_atom_section(section, expected_head: str) -> str:
    if (
        not isinstance(section, tuple)
        or len(section) != 2
        or section[0] != expected_head
        or not isinstance(section[1], str)
    ):
        raise GenerationError(
            f"protocol IR envelope requires ({expected_head} VALUE), got {section!r}"
        )
    return section[1]


def parse_protocol_envelope(
    source: str, descriptor: ProtocolExportDescriptor
) -> ProtocolEnvelope:
    """Parse and validate a canonical Rocq protocol IR envelope.

    Validation happens before a protocol-specific decoder or renderer sees the
    program. This prevents a generator from silently consuming the wrong
    protocol, schema revision, or IR language revision.
    """

    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", descriptor.protocol_id):
        raise GenerationError(
            f"protocol id is not a safe S-expression atom: {descriptor.protocol_id!r}"
        )
    envelope = parse_sexpr(source)
    if len(envelope) != 6 or envelope[0] != "protocol-ir":
        raise GenerationError(
            "protocol IR export must have exactly the canonical "
            "(protocol-ir schema ir id signature program) envelope"
        )

    schema_atom = _single_atom_section(envelope[1], "schema-version")
    ir_atom = _single_atom_section(envelope[2], "ir-version")
    protocol_id = _single_atom_section(envelope[3], "protocol-id")
    if not schema_atom.isdecimal():
        raise GenerationError(f"schema version must be a natural number: {schema_atom!r}")
    if not ir_atom.isdecimal():
        raise GenerationError(f"IR version must be a natural number: {ir_atom!r}")

    schema_version = int(schema_atom)
    ir_version = int(ir_atom)
    if schema_version != descriptor.schema_version:
        raise GenerationError(
            f"protocol IR schema version mismatch: expected "
            f"{descriptor.schema_version}, got {schema_version}"
        )
    if ir_version != descriptor.ir_version:
        raise GenerationError(
            f"protocol IR language version mismatch: expected "
            f"{descriptor.ir_version}, got {ir_version}"
        )
    if protocol_id != descriptor.protocol_id:
        raise GenerationError(
            f"protocol id mismatch: expected {descriptor.protocol_id!r}, "
            f"got {protocol_id!r}"
        )

    signature = envelope[4]
    program = envelope[5]
    if not isinstance(signature, tuple) or not signature or signature[0] != "signature":
        raise GenerationError("protocol IR envelope requires a signature section")
    if not isinstance(program, tuple) or not program or program[0] != "program":
        raise GenerationError("protocol IR envelope requires a program section")
    return ProtocolEnvelope(
        protocol_id=protocol_id,
        schema_version=schema_version,
        ir_version=ir_version,
        signature=signature,
        program=program,
        raw=envelope,
    )


def evaluate_protocol_export(
    *,
    rocq_project: Path,
    theories: Path,
    descriptor: ProtocolExportDescriptor,
    coqtop: RocqReplCommand,
    rocqlib: Path | None,
    description: str,
) -> tuple[ProtocolEnvelope, str]:
    """Evaluate one formal program and validate its envelope before dispatch."""

    (source,) = evaluate_string_exports(
        rocq_project=rocq_project,
        theories=theories,
        logical_root=descriptor.logical_root,
        imports=descriptor.imports,
        exports=(descriptor.export,),
        coqtop=coqtop,
        rocqlib=rocqlib,
        description=description,
    )
    return parse_protocol_envelope(source, descriptor), source


def render_protocol_data_module(
    envelope: ProtocolEnvelope,
    source: str,
    *,
    generated_by: str,
) -> str:
    """Render a Python module containing only validated protocol IR data.

    The generated artifact deliberately has no imports, functions, classes, or
    protocol semantics.  A reusable runtime decodes ``PROTOCOL_TREE``.
    """

    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    tree = pprint.pformat(envelope.raw, width=88, compact=False, sort_dicts=False)
    return (
        '"""Generated protocol IR data; do not edit by hand."""\n\n'
        f"# Generated by {generated_by}.\n"
        f"PROTOCOL_ID = {envelope.protocol_id!r}\n"
        f"SCHEMA_VERSION = {envelope.schema_version}\n"
        f"IR_VERSION = {envelope.ir_version}\n"
        f"ROCQ_PROGRAM_DIGEST = {digest!r}\n\n"
        f"PROTOCOL_TREE = {tree}\n"
    )


def write_or_check(path: Path, content: str, check: bool) -> bool:
    """Check freshness or atomically replace one generated artifact."""

    if check:
        return path.is_file() and path.read_text(encoding="utf-8") == content
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(content)
            output.flush()
            os.fsync(output.fileno())
        permissions = (path.stat().st_mode & 0o777) if path.exists() else 0o644
        os.chmod(temporary_path, permissions)
        os.replace(temporary_path, path)
    except BaseException:
        temporary_path.unlink(missing_ok=True)
        raise
    return True
