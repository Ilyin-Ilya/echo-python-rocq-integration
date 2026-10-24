# Echo Python–Rocq reproducibility guide

Run all commands from `/Users/iilin/echo-python-rocq-integration` or from an
equivalent unpacked artifact root.

## 1. Rocq proof

```console
make -C echo-algorithm-coq \
  COQBIN="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin" \
  ROCQLIB="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/lib/coq" \
  -j2
```

Expected result: all maintained generic-IR theories compile, including
`EchoIRExecutable.v`, the direct `EchoIRExecutable*.v` invariant chain, and
`EchoIRSpanningTree.v`. The integration theories contain no `Admitted`,
`admit`, or added `Axiom`.

The primary checked chain is:

```text
EchoIRProgram.echo_program interpreted by the generic IR interpreter
  -> direct generic-IR step and reachability evidence
  -> direct safety, accounting, and obligation invariants
  -> generic runner completion
  -> direct generic-IR spanning tree
```

## 2. Python tests

```console
cd distributed-simulations
python3 -m unittest discover -s tests -v
```

Expected result: 87 maintained tests pass without importing the historical
oracle module.

## 3. Maintained Rocq-to-Python generation freshness

From the artifact root:

```console
make generated
```

Expected result: the production Python executable matches the compiled
`EchoIRExport.v` value, and the exported IR capabilities match the compiler.

The historical Echo-specific implementation and its comparison vectors are a
separate optional gate:

```console
make compare
```

Expected result: `checked data-only Echo migration oracles (10 steps, 7
runs)`, with program
digest `80c364ddf54b53350aab398b0dc56688d1e59503736574ca05e630ddec16e6df`,
and vector digest
`60c41d4cd5d6a46074153ccaa32041e3f0f42cfa61a8b0790deac6b5b9f1a220`,
and run-vector digest
`e17e8baaf3c51c66e3422eba8e7c4107f1d4361324bb63826c65dbd733a13b89`.
The optional command fails if the compiled Rocq export is stale, the
historical export differs, the Rocq-computed vector export differs, or
generated Python was manually edited. The comparison suite executes all ten
Rocq-computed step results and all seven Rocq-computed run results against the
generic interpreter and generated executable. It currently runs 15 optional
migration tests.

## 4. Versioned trace and generated-core replay

```console
cd distributed-simulations
python3 main.py echo --seed 23 --log /tmp/echo.jsonl
python3 -m distributed_simulations.algorithms.echo_trace /tmp/echo.jsonl
```

Expected checker output contains `"valid": true` and the same transition count
as the simulator result. The trace schema is documented in
`ECHO_TRACE_SCHEMA.md`. Its v2 header pins the exact Rocq program,
single-step-vector, and full-run-vector SHA-256 digests used by the generated
core.

## 5. Exhaustive bounded exploration

```console
python3 -m distributed_simulations.algorithms.echo_evaluation
```

Expected highlights:

| Case | States | Transitions | Stuck | Unsafe |
|---|---:|---:|---:|---:|
| line-5 | 9 | 8 | 0 | 0 |
| binary-tree-7 | 121 | 308 | 0 | 0 |
| ring-5 | 125 | 200 | 0 | 0 |
| dense-4 | 14,468 | 56,613 | 0 | 0 |

The same run must detect all five controlled mutations. The checked-in report
is `ECHO_EXPLORATION_REPORT.md`.

## 6. One-command integration gate

All maintained checks above are combined in:

```console
make verify
```

Set `COQBIN` and `ROCQLIB` if the Rocq tools and library are not on their
default paths. The script stops at the first failed proof, stale generated
artifact, test, trace replay, or bounded evaluation command.

## Trusted boundary

- Rocq checks the generic IR interpreter, direct Echo reachability invariants,
  runner outcomes, and complete-run spanning-tree theorem.
- `echo_exec` is definitionally the generic interpretation of the first-order
  `EchoIRProgram.echo_program`; the serializer and Python-generation backend
  remain trusted.
- The generic Python compiler, generated-function runtime, scheduler,
  topology/trace conversion, snapshot serialization, and thin entry point
  remain trusted implementation code.
- Message loss, process crashes, in-handler interleavings, and fairness are not
  modeled.
- The decision theorem assumes a finite connected undirected irreflexive graph
  represented by the proof-only rooted-depth witness described in the semantic
  contract. This is a Rocq topology witness, not a Python event certificate.
- The other three Python case studies are dynamically checked but are not
  covered by the Echo theorem.
