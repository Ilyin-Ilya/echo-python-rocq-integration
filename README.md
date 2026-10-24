# Python–Rocq distributed-protocol integration

[![Verify Rocq and Python integration](https://github.com/Ilyin-Ilya/echo-python-rocq-integration/actions/workflows/verify.yml/badge.svg)](https://github.com/Ilyin-Ilya/echo-python-rocq-integration/actions/workflows/verify.yml)

This project demonstrates one maintainable way to connect a proved Rocq
protocol with an ordinary Python application. Echo is the first protocol
implemented with the architecture.

If you are new to the project, read [`START_HERE.md`](START_HERE.md). It
explains the runtime data flow, proof boundary, trusted code, and normal edit
workflow.

## Architecture

There is one maintained source of Echo transition behavior:
`echo-algorithm-coq/theories/EchoIRProgram.v`.

```text
generic typed IR kernel in Rocq
             |
EchoIRProgram.v + direct proofs
             |
validated Rocq export
             |
protocol-neutral Python compiler
             |
generated_echo_executable.py
             |
thin scheduling, tracing, and public-API adapter
```

The generated module contains ordinary Python guard and action functions. The
production runner calls those functions directly; it does not interpret the
serialized IR tree instruction by instruction.

Human-written Python is responsible for topology conversion, choosing which
queued message to deliver, logging, CLI handling, and result presentation. It
does not choose an Echo rule or construct a successor state.

## Repository layout

```text
echo-python-rocq-integration/
├── echo-algorithm-coq/       Rocq IR, Echo program, and proofs
├── distributed-simulations/ Python compiler, runtime, adapter, and tests
├── docs/current/             maintained contracts, reports, and guides
├── START_HERE.md             canonical maintainer guide
├── Makefile
└── verify_echo_integration.sh
```

The checkout is self-contained: a fresh clone needs only the top-level
repository and the documented Rocq and Python tools.

## Run the project

```console
make quick
make verify
```

- `make quick` checks generated-file freshness and runs the maintained Python
  suite.
- `make verify` builds the maintained Rocq proofs and runs the complete
  integration gate.
- `make compare` separately builds and checks the preserved historical
  Echo-specific implementation and migration oracles.
- `make evaluate` explores bounded delivery schedules and controlled
  mutations.

Set `COQBIN` and `ROCQLIB` if Rocq is not available on `PATH`; see
[`ECHO_REPRODUCIBILITY.md`](docs/current/ECHO_REPRODUCIBILITY.md).

The maintained Python suite currently contains 87 tests. The optional
migration suite adds 15 serialized-program and historical-oracle comparisons,
for 101 tests in total, and is run separately by `make compare`.

## Make a protocol change

1. Edit `echo-algorithm-coq/theories/EchoIRProgram.v` and, when necessary,
   `EchoIRSignature.v`.
2. Repair the affected Rocq proofs.
3. Run `make regenerate` to compile the validated Rocq export into Python.
4. Run `make verify`.

Never edit
`distributed-simulations/distributed_simulations/algorithms/generated_echo_executable.py`
by hand. It is deterministic generated output and its freshness is checked.

For scheduler, trace, CLI, or host-application changes, edit the handwritten
Python normally and run at least `make quick`.

## Documentation

The maintained end-user documentation is:

- [`START_HERE.md`](START_HERE.md) — detailed architecture and trust boundary.
- [`PROTOCOL_ADAPTER_GUIDE.md`](docs/current/PROTOCOL_ADAPTER_GUIDE.md) — what remains
  handwritten for a new protocol.
- [`ECHO_SEMANTIC_CONTRACT.md`](docs/current/ECHO_SEMANTIC_CONTRACT.md) — Rocq/Python
  transition correspondence.
- [`ECHO_TRACE_SCHEMA.md`](docs/current/ECHO_TRACE_SCHEMA.md) — trace representation.

The optional Echo-specific executable, its internal proofs, and its oracle
exports are listed only in `echo-algorithm-coq/_CoqProject.migration`. The
older exact-state agreement files remain for reference but are no longer
built: certificate removal deliberately transferred list-order ownership from
the caller to the maintained Rocq program, so their old equality statement is
not valid. The oracle comparison remains useful migration evidence, not a
second production implementation.
