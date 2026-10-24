#!/bin/sh
set -eu

artifact_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
rocq_project="$artifact_root/echo-algorithm-coq"
python_project="$artifact_root/distributed-simulations"
verification_tmp=$(mktemp -d "${TMPDIR:-/tmp}/echo-integration.XXXXXX")
trap 'rm -rf -- "$verification_tmp"' EXIT HUP INT TERM

export PYTHONPYCACHEPREFIX="$verification_tmp/pycache"

rocq_platform_root="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources"
if [ -z "${COQBIN:-}" ] && [ -x "$rocq_platform_root/bin/rocq" ]; then
    COQBIN="$rocq_platform_root/bin/"
fi
if [ -z "${ROCQLIB:-}" ] && [ -d "$rocq_platform_root/lib/coq" ]; then
    ROCQLIB="$rocq_platform_root/lib/coq"
fi

printf '%s\n' '==> Building the Rocq development'
if [ -n "${COQBIN:-}" ] || [ -n "${ROCQLIB:-}" ]; then
    make -C "$rocq_project" COQBIN="${COQBIN:-}" ROCQLIB="${ROCQLIB:-}"
else
    make -C "$rocq_project"
fi

printf '%s\n' '==> Checking the generic protocol IR envelope'
(
    cd "$python_project"
    python3 tools/check_protocol_ir_export.py
)

printf '%s\n' '==> Checking the maintained Rocq-to-Python generated artifact'
(
    cd "$python_project"
    python3 tools/generate_echo_program_from_rocq.py --check
)

printf '%s\n' '==> Running Python unit and integration tests'
(
    cd "$python_project"
    python3 -m unittest discover -s tests -v
)

printf '%s\n' '==> Replaying a generic-IR runtime trace'
(
    cd "$python_project"
    python3 main.py echo --seed 23 --log "$verification_tmp/echo.jsonl" \
        > "$verification_tmp/run.json"
    python3 -m distributed_simulations.algorithms.echo_trace \
        "$verification_tmp/echo.jsonl"
)

printf '%s\n' '==> Running bounded schedule and mutation evaluation'
(
    cd "$python_project"
    python3 -m distributed_simulations.algorithms.echo_evaluation --json \
        > "$verification_tmp/evaluation.json"
)

printf '%s\n' 'Echo Rocq-to-Python integration verification passed.'
