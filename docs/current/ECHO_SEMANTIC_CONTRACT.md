# Echo semantic contract

## Purpose

This document describes the one maintained Echo execution model shared by
Rocq and Python. Protocol behavior is authored once as generic typed IR data in
`EchoIRProgram.v`. Rocq's generic interpreter executes that value through the
public `EchoIRExecutable.v` API; the deterministic generator serializes the
same value for Python's generic interpreter.

The contract covers configuration, protocol state, one event, complete-run
outcomes, and the handwritten scheduling boundary. CLI formatting, JSON I/O,
the PRNG implementation, and wall-clock behavior are outside the formal model.

## Canonical configuration and state

`ProtocolIRTypes.v` defines the protocol-neutral execution data. Echo gives
those generic fields and messages concrete identifiers in `EchoIRSignature.v`:

- `echo_config`: initiator, finite ordered node list, and adjacency function;
- `echo_process`: optional parent, ordered pending neighbors, and `finished`;
- `echo_message`: unique numeric ID, request/reply kind, sender, and receiver;
- `executable_echo_state`: process map, message store, startup flag, and next
  message ID; and
- `echo_event`: startup, or delivery of one selected queued message ID. There
  are no Echo ordering or parent inputs.

Configured neighbor order controls deterministic request emission. On a first
request, the program removes the sender from that list; on a reply, it reads
the receiver's installed parent from formal state. Store order is visible to
the scheduler but does not restrict the correctness theorem: any queued
message may be selected.

The canonical initial state has every process equal to
`initial_echo_process`, an empty store, `started = false`, and next ID 1.
Startup validity is checked inside `echo_exec` over the configured node list;
callers do not supply a proof or a second initialization predicate.

## Sole maintained transition definition

The executable semantics is:

```coq
echo_exec config state event : ir_step_result node echo_ir_signature
```

`echo_exec` interprets the nine-rule generic `echo_program`. A failed result
means that the event is rejected and cannot mutate state. The logical step
evidence is derived from the same generic-interpreter result; it does not
restate the rule behavior.

```coq
echo_exec config state event = IRStepSuccess rule_id successor
```

There is no separately maintained Python transition relation, replay
function, validity checker, or `execute_echo` wrapper. The old
`EchoTransitionIR.v` implementation is retained only in
`_CoqProject.migration` as historical comparison evidence.

## Nine accepted event forms

### 1. Startup

The state must be canonical-initial, and the supplied ordered nodes must be a
permutation of the initiator's configured neighbors. The initiator becomes
started, its pending list becomes that order, and one request is emitted to
each neighbor with consecutive IDs.

### 2. First request at a non-leaf participant

The selected queued request targets an initial non-initiator. The supplied
forward list must be a nonempty permutation of the receiver's neighbors after
removing the sender. The sender becomes the parent, the forward list becomes
pending, and one request is emitted to every pending neighbor.

### 3. First request at a leaf participant

The selected queued request targets an initial non-initiator with no neighbor
other than the sender. The sender becomes the parent, the participant becomes
finished, and one reply is emitted to its parent.

### 4. Repeated request at a participant

The selected queued request targets a non-initiator that already has a parent
or is finished. Local state is unchanged and one reply is emitted to the
sender.

### 5. Request returned to the initiator

The selected queued request targets a started, unfinished initiator. Root
state is unchanged and one reply is emitted to the sender.

### 6. Non-final participant reply

The selected queued reply's sender is pending at a non-initiator, the event's
parent matches the installed parent, at least one pending neighbor remains,
and the participant is unfinished. The sender is removed from pending and no
message is emitted.

### 7. Final participant reply

The same checks hold, but removing the sender empties pending. The participant
becomes finished and emits one reply to its parent.

### 8. Non-final initiator reply

The selected queued reply's sender is pending at the started, parentless,
unfinished initiator, and another pending neighbor remains. The sender is
removed and no message is emitted.

### 9. Final initiator reply

Removing the valid sender empties the initiator's pending list. The initiator
becomes finished and emits no message.

Every delivery removes exactly the selected message ID, preserves unselected
messages, appends newly emitted messages, and advances the next-ID counter by
the number emitted.

## Completion and runner outcomes

Completion requires:

- startup has occurred;
- the initiator has no pending neighbors;
- the canonical store is empty; and
- the initiator is finished, unless it has no configured neighbors.

The last clause gives singleton graphs the same public completion theorem
without accepting a malformed unfinished multi-node state.

`EchoRunner.v` defines a total, fuel-bounded schedule runner with four
outcomes:

- `complete`: the completion predicate holds;
- `stuck`: startup occurred, the store is empty, but completion is false;
- `bounded`: fuel or the supplied schedule ended first; and
- `invalid-choice`: the selected event was rejected, leaving state unchanged.

Schedules contain events, never successor states. Every successful successor
is computed by `echo_exec`.

## Python execution boundary

`generated_echo_executable.py` contains the compiled Echo constants, guards,
actions, initialization, completion, step, and event constructors.
`protocol_compiled_runtime.py` supplies protocol-neutral values and update
primitives used by those functions. Normal `run_echo` delegates once to the
handwritten scheduling layer in `echo_execution.py`.

Handwritten Python performs only:

1. topology validation and conversion to the generic configuration;
2. seeded selection of one message already in the generic store;
3. observation of immutable generic states for logging; and
4. conversion of the terminal result to the common CLI shape.

The scheduler chooses only a queued message ID. Generated guards select the
rule and generated actions compute the successor. Python has no second live
Echo state, queue, mutable Echo roles, certificates, or encode/install loop.

The old serialized program, interpreter adapter, and generated oracles live
under `distributed_simulations/migration/`. They are separate migration
evidence imported only by comparison tests.

## Topology obligations

Public execution validates:

- a nonempty finite unique node set;
- exactly one initiator;
- known, duplicate-free neighbor lists;
- no self-edge;
- symmetric adjacency; and
- connectivity from the initiator.

The Rocq spanning-tree theorem uses the corresponding finite, symmetric,
irreflexive, connected configuration assumptions.

## Formal result

The maintained proof chain is:

```text
accepted runner event
  -> the Rocq generic IR interpreter returns one rule ID and successor
  -> direct generic-IR step evidence
  -> direct generic-IR reachability and invariants
  -> generic runner completion
  -> every configured node has a parent path to the initiator
```

`EchoIRSpanningTree.v` states the final completion theorem directly over the
generic IR state. It covers singleton and non-singleton connected topologies.
The historical `EchoExecutableSpanningTree.v`, abstraction, and refinement
files are preserved only in the optional migration project.

## Cross-language checks and trusted boundary

The maintained Rocq build exports:

- the versioned generic signature and nine-rule Echo IR program;
- one computed input/result fixture for each of the nine generic rules; and
- a computed complete two-node generic run.

The normal Python gate replays these maintained fixtures and imports no data
from the historical executable.

The protocol-neutral runtime decodes exported states, configurations, and
events and canonically re-encodes Python states, events, step results, and run
outcomes. The gate uses this same API for Echo and compares the non-Echo
counter's initial state and complete run directly with Rocq-computed exports.

Rocq also exports a versioned capability manifest linked to exhaustive matches
over the actual typed expression and action syntax. Generation and production
loading reject the program unless Python declares exactly the same IR types,
expression constructors, action constructors, and event patterns. This turns
constructor additions or renames into an explicit compatibility failure rather
than allowing unsupported syntax to remain latent.

The optional migration build additionally exports ten historical computed
single-step results and seven historical computed complete-run results.

The generators embed SHA-256 digests for each export. Python re-executes all
historical vectors only during `make compare`, which rejects stale or manually
edited artifacts. Bounded
all-delivery-order exploration and five controlled mutations add empirical
coverage.

Rocq proves properties of `echo_exec`, not of the generated Python executable.
The S-expression parser, generic Python compiler, generated-function runtime,
topology/trace conversion, scheduler, observer, and JSON encoding remain
trusted implementation code. The tests and digests reduce this risk but do
not turn it into a kernel proof.

Message loss, crashes, in-handler interleavings, and fairness are not modeled.
