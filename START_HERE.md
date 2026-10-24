# Start here: how the Python and Rocq Echo models connect

## The short version

There is now one maintained source of Echo transition behavior: the generic
IR program authored in Rocq. A protocol-neutral compiler turns that program
into ordinary Python transition functions.

```text
Rocq Echo IR program + proofs
  |  exported, validated, and compiled
  v
generated_echo_executable.py (ordinary Python functions)
  |  uses protocol-neutral runtime primitives
  v
echo.py + echo_execution.py: topology conversion, scheduling,
logging, result conversion, trace, and CLI
```

This does not try to generate a whole application. Humans still write the Rocq
protocol program and useful proofs, plus small Python adapters for application
I/O and policy. Mechanical export, compilation, validation, execution, replay,
and freshness checking are automated. A serialized program and interpreter
remain only as migration evidence. See
`docs/current/PROTOCOL_ADAPTER_GUIDE.md`.

## What to edit

For an Echo protocol change:

1. Edit the generic Echo program in
   `echo-algorithm-coq/theories/EchoIRProgram.v`.
2. Build Rocq and repair any proof that no longer holds: `make proof`.
3. Regenerate the production executable:
   `cd distributed-simulations && python3 tools/generate_echo_program_from_rocq.py`.
4. Run `make verify` from this directory.

The normal workflow deliberately does not touch migration data. If you are
comparing against the retired Echo-specific model, run
`make regenerate-migration` and then `make compare` explicitly.

For a generic type or instruction change, update the `ProtocolIR*.v` kernel,
the generic Python compiler/runtime, the Rocq interpreter, and the versioned
serializer. For Echo-only fields or rules, update `EchoIRSignature.v` and
`EchoIRProgram.v`.

Never edit `generated_echo_executable.py` or the migration-only
`generated_echo_program.py` by hand. Freshness checks reject manual edits or
generated files that no longer match the compiled Rocq export.

For scheduler, logging, CLI, or generic runtime changes, edit Python normally,
then run at least `make quick`. If the change affects Echo state, queue, or
message representation, run the full `make verify` gate.

## What each boundary file does

| File | Responsibility |
|---|---|
| `EchoTopology.v` | neutral configuration and topology interface shared by the maintained Echo IR proofs; defines no Echo state or transition semantics |
| `LTS.v`, `Network.v`, `EchoAlgorithm.v`, `EchoCorrectness.v`, `Example.v` | preserved historical relational Echo model and proof stack; built only by `make compare`/`make migration` |
| `EchoExecutable*.v`, `EchoTransitionIR*.v`, `EchoRunner*.v` | preserved historical Echo-specific executable and proof stack; built only by `make compare`/`make migration` |
| `EchoIRSpanningTree.v` | generic-IR completion and complete-run theorem: every configured node's IR parent path reaches the initiator |
| `EchoIRConfig.v` | direct construction of the generic Echo IR runtime configuration from nodes, initiator, and adjacency; contains no old executable state or simulation relation |
| `EchoIRSafety.v` | generic-IR topology, parent/lifecycle, pending-list, local completion, finished-root queue, and small-cycle safety theorems |
| `EchoIRAccounting.v` | generic-IR discovery and request/reply accounting: discovered participants are parented, directed request edges are unique, parent-directed requests are excluded, reply receivers are discovered, and reverse request/reply pairs cannot coexist |
| `EchoIRObligations.v` | generic-IR queue/pending correspondence and propagation: replies originate from discovered/finished processes as appropriate, directed reply edges are unique, unfinished children stay pending, and every pending or queued obligation reaches the initiator |
| `EchoIRSpanningTreeExamples.v` | legacy-free computed generic-run instantiation of the direct spanning-tree and safety interfaces |
| `EchoEvaluationVectorsExport.v`, `EchoRunnerVectorsExport.v` | optional migration-only exports for the committed historical comparison vectors |
| `ProtocolIR*.v` | protocol-neutral typed language, interpreter, runner, proofs, and serializer |
| `EchoIRProgram.v` | the Echo program expressed as generic IR data |
| `EchoIRExecutable.v` | legacy-free public API: the generic `echo_program`, initializer, `echo_exec`, step evidence, queued-delivery facts, reachability, completion/stuck predicates, runner soundness, and the first direct reachable-state allocator invariant |
| `EchoIRExecutableInvariants.v` | direct, legacy-free rule-effect proofs over the generic program; proves that the initiator remains parentless across all nine rules and all reachable states |
| `EchoIRExecutableLifecycle.v` | reusable three-field process-update abstraction and direct proof that every finished non-initiator has an installed parent across all nine rules and all reachable states |
| `EchoIRExecutablePending.v` | direct proof that reachable pending lists are duplicate-free configured-neighbor lists across all nine rules |
| `EchoIRExecutableDiscovery.v` | direct all-nine-rule accounting proof that every discovered non-initiator has an installed parent |
| `EchoIRExecutableTopology.v` | joint direct invariant proving installed parent edges and queued messages follow the generic configured topology across all nine rules |
| `EchoIRExecutableRequestAccounting.v` | direct all-nine-rule proof that queued request edges stay unique; couples edge uniqueness with sender provenance so first-discovery request batches are fresh |
| `EchoIRExecutableRequestParent.v` | direct all-nine-rule consumed-parent-request proof: jointly maintains queued request accounting, fresh unique IDs, causal parent-source provenance, and exclusion of queued requests from installed parents; the public accounting theorem no longer uses backward simulation |
| `EchoIRExecutableReplyDiscovery.v` | direct all-nine-rule proof that queued replies target discovered processes; jointly tracks configured parent targets and queued request senders as the causal support invariant |
| `EchoIRExecutableRequestReply.v` | direct all-nine-rule proof that queued requests cannot coexist with replies on their reverse edges; composes unique IDs, request-edge uniqueness, consumed-parent separation, and discovery support |
| `EchoIRExecutableObligations.v` | direct obligation layer; proves queue/pending and completion obligations through all nine rules, preserves a proof-only rooted parent-chain certificate, propagates pending obligations to the initiator, and derives no-self/no-mutual-parent consequences without legacy backward simulation |
| `EchoIRExecutableSpanningTree.v` | legacy-free direct spanning-tree proof; preserves the discovery frontier through all nine generated rules and proves a finished reachable root gives every configured node a finite parent path to the initiator |
| `EchoIRExecutableExamples.v` | computed two-node execution and allocator-invariant checks through only the public generic API; imports no old Echo transition or compatibility module |
| `protocol_ir_python_compiler.py` | protocol-neutral compiler from the exported typed IR into readable Python functions |
| `protocol_values.py` | immutable protocol configuration, state, messages, events, results, and runtime-value validation shared by compiled and interpreted execution |
| `protocol_ir_ast.py` | typed protocol syntax and capability manifest; contains no decoding or execution logic |
| `protocol_ir_codec.py` | validated conversion between Rocq S-expressions, the typed AST, and runtime values; contains no execution logic |
| `protocol_ir_interpreter.py` | protocol-neutral reference evaluator and runner used for independent conformance and migration checks, not production generated execution |
| `protocol_ir.py` | compatibility facade that re-exports the split AST, values, codec, and interpreter APIs for existing callers |
| `generated_echo_executable.py` | generated production module containing Echo constants, guards, actions, completion, initialization, and event constructors |
| `protocol_compiled_runtime.py` | protocol-neutral runtime primitives used by generated functions |
| `echo.py` | small public `run_echo` facade: validates input, invokes execution, and formats the result |
| `echo_execution.py` | scheduler and optional trace observer; chooses only which queued message to deliver |
| `echo_codec.py` | converts topology and trace values to/from generic IR values; contains no Echo behavior |
| `echo_trace.py` | replays states with the same generated transition functions and checks program/version identity |
| `migration/` | serialized generic program, interpreter adapter, and historical computed oracles retained for explicit comparison tests only |

## What is proved, checked, and trusted

The maintained formal chain is now direct:

```text
scheduled external event
  -> generated step function finds one enabled generated rule
  -> generated action function computes the only successor
  -> direct all-rule IR invariants, including the discovery frontier
  -> generated completion predicate
  -> every configured node has an IR parent path to the initiator
```

The schedule cannot directly supply or mutate the successor state. A rejected
event produces an invalid-choice outcome; a successful event advances only to
the state returned by the interpreted Rocq program. The direct IR runner proofs
cover outcome classification, reachability, and complete-run spanning-tree
correctness. Seven serialized historical full-run vectors remain as migration
oracles and are re-executed by Python through the migration interpreter. The Python
runner starts from generated IR initialization and lets a scheduler choose
only an already queued message; generated guards select the rule and generated
actions compute every successor. State snapshots exposed to callbacks are
immutable.

Phase 6 has switched production simulation to this complete execution surface.
`run_echo` delegates once to `execute_generated_echo`. The generated `State`
and its store are the only live Echo state and queue; handwritten Python
supplies only topology, message scheduling, observation, and output conversion.

`EchoExecutableRefinement.v` supplies the reusable branch proofs used
internally by that direct canonical theorem. The old Python-shaped
transition/replay/decision chain has been removed.

The following code is still trusted implementation code rather than proved by
the Rocq kernel:

- the small S-expression parser and Python compiler;
- the protocol-neutral Python runtime used by generated functions;
- topology/trace conversion in `echo_codec.py`;
- the seeded scheduler, trace JSON encoder, and thin Python entry point.

The gate reduces this risk with exact generation hashes, ten Rocq-computed
single-step vectors, seven Rocq-computed full-run vectors, Python integration
tests, trace replay, and bounded all-delivery-order exploration. Those checks
are strong evidence, not a proof of the entire Python interpreter or runtime.

The maintained call has no caller-supplied initialization or rule decision:

```coq
echo_exec config state event : ir_step_result node echo_ir_signature
```

`make_echo_ir_config` supplies the initiator, finite node list, and adjacency
function. On startup, the generated start rule checks that every configured
process is initial. Public IR proofs, generation, and the Python runner use
this surface directly; no compatibility wrapper remains in the maintained
build.

## The singleton boundary

The canonical `EchoRunComplete` spanning-tree theorem now covers a one-node
graph through the same public theorem as every other connected topology.
`run_echo()` therefore reports the same proof scope for singleton and
non-singleton runs:

```json
{
  "canonical_runner_proof_covered": true,
  "verification_scope": "runtime-check-and-canonical-runner-proof"
}
```

The ordinary `verified` field continues to mean that the completed runtime
parent structure passed Python's structural verifier; it must not be read as
“the whole Python program was formally verified.”

## Traces are reproducible, not independent

Trace schema v2 records the topology digest and SHA-256 digests of the exact
Rocq rule program, single-step vectors, and full-run vectors. The replay
checker rejects a trace produced by different generated semantics.

The replay checker intentionally uses the same generated transition core as
the runtime. It catches scheduling, serialization, and trace tampering; it
is not an independent second implementation. The Rocq proofs and evaluation
vectors are the separate semantic checks.

## One-command entry points

```console
make quick   # maintained generated-file freshness + focused Python tests
make compare # optional legacy build, oracle freshness, and comparison tests
make verify  # maintained Rocq proofs + generation + tests + trace + exploration
```

The historical executable and its internally scoped proofs are optional:

```console
cd echo-algorithm-coq
make migration
```

They are listed only in `_CoqProject.migration`; the normal `_CoqProject` and
`make verify` proof boundary exclude the entire old Echo-specific executable
and its export vectors. The retired `EchoIRCompatibility`, forward/backward
simulation, and program-example files remain in the repository as migration
history but are not built. Their exact-state theorem predates certificate
removal and is no longer true because the maintained IR owns list ordering.

`make compare` is the focused migration command. It builds the historical
executable and oracle proofs, checks generated vectors, and re-executes them
through the migration interpreter. It does not claim exact state equality for
all schedules and does not introduce a second production Python implementation.

If Rocq is not on `PATH`, pass `COQBIN` and `ROCQLIB` to `make`, as documented
in `docs/current/ECHO_REPRODUCIBILITY.md`.

The combined directory is a self-contained top-level repository. Maintained
contracts, reports, and reproducibility instructions live in `docs/current/`.
