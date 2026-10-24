# Rocq development for the generated Echo implementation

This directory contains the formal half of the Rocq-to-Python integration.
The maintained source of Echo behavior is `theories/EchoIRProgram.v`: an Echo
program written in the generic typed IR defined by the `ProtocolIR*.v` files.
Rocq interprets and proves properties of that program, while the root build
exports the same program and compiles it into ordinary Python functions.

For the end-to-end architecture and editing workflow, start with
[`../START_HERE.md`](../START_HERE.md).

## Build

From the integration repository root, run:

```console
make verify
```

That command rebuilds the maintained Rocq development, checks generated Python,
runs the Python tests, replays a trace, and performs bounded schedule and
mutation evaluation.

To build only the maintained Rocq files from this directory:

```console
make
```

If Rocq is not on `PATH`, pass `COQBIN` and `ROCQLIB`; both this Makefile and the
root Makefile accept them. Generated `Makefile.coq` files are build artifacts
and are not versioned.

The older relational Echo model is preserved for comparison, not used by the
production proof or generation chain. Build it explicitly from the root with:

```console
make compare
```

## Maintained proof chain

| Files | Responsibility |
|---|---|
| `ProtocolIRTypes.v`, `ProtocolIRExpressions.v`, `ProtocolIRActions.v` | Generic typed protocol language |
| `ProtocolIRInterpreter.v`, `ProtocolIRRunner.v` | Generic Rocq semantics and bounded execution |
| `ProtocolIRExport.v` | Versioned serialization consumed by the generator |
| `EchoTopology.v` | Echo configuration and graph obligations; no state or transition semantics |
| `EchoIRSignature.v` | Echo-specific state, event, message, and configuration fields |
| `EchoIRProgram.v` | The maintained Echo rules, guards, actions, initialization, and completion predicate |
| `EchoIRExecutable*.v` | Direct rule-effect, reachability, accounting, obligation, and spanning-tree proofs for the generic IR program |
| `EchoIRSafety.v`, `EchoIRAccounting.v`, `EchoIRObligations.v`, `EchoIRSpanningTree.v` | Small public theorem interfaces over the direct proofs |
| `EchoIRExport.v` | Echo export entry point used by Python generation |
| `EchoIRConformance.v`, `EchoIRRuleUniqueness.v` | Conformance and unambiguous-rule results |
| `MoA*.v` | Independent Mathematics of Arrays formalization |

The maintained source list is `_CoqProject`. In particular, it does not import
`EchoAlgorithm.v` or `EchoCorrectness.v`; therefore the current proof chain does
not secretly rely on a second Echo transition implementation.

## What the main result says

The direct generic-IR development proves safety properties for every reachable
state and every enabled delivery order. Its completion theorem states that when
a reachable run satisfies the generated completion predicate, every configured
node has a finite parent path to the initiator. The proof covers all nine Echo
rules expressed in `EchoIRProgram.v`.

The development contains no `Admitted`. The build checks the central exported
results with `Print Assumptions`; they are closed under the declared
configuration hypotheses.

This is a safety and partial-correctness result. It does not assume fairness and
does not claim that an arbitrary scheduler must eventually deliver every queued
message.

## Historical migration stack

`_CoqProject.migration` contains the earlier relational/executable model:

- `LTS.v`, `Network.v`, `EchoAlgorithm.v`, `EchoCorrectness.v`, and `Example.v`;
- `EchoExecutable*.v`, `EchoTransitionIR*.v`, and `EchoRunner*.v`.

These files remain useful as independent migration evidence. `make compare`
rebuilds them, checks the committed Rocq-computed vectors, and compares those
vectors with the current Python execution. They are not production imports.

The retired exact-state bridge files (`EchoIRCompatibility.v`,
`EchoIRForwardSimulation.v`, `EchoIRBackwardSimulation.v`, and
`EchoIRProgramExamples.v`) are retained as source history but intentionally
excluded from both builds. Their equality statement predates removal of
caller-supplied ordering certificates.

For the older relational proof narrative, see
[`PROOF_EXPLAINED.md`](PROOF_EXPLAINED.md). For the independent MoA work, see
[`MOA_FORMALIZATION.md`](MOA_FORMALIZATION.md).

## Citation and license

Release metadata is in [`CITATION.cff`](CITATION.cff). The source is available
under the [MIT License](LICENSE).
