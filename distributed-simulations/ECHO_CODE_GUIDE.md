# Reading the generated Echo implementation

This guide is for a Python engineer who wants to understand Echo without first
learning the Rocq exporter or the generic IR encoding.

## The four files that matter

Read the implementation in this order:

1. `distributed_simulations/algorithms/echo.py` is the public facade. It
   validates a topology, calls the execution adapter, validates the result,
   and presents the final parent tree.
2. `distributed_simulations/algorithms/generated_echo_executable.py` contains
   the actual Echo rules. It is generated from Rocq, but it is ordinary Python:
   `_check_*` functions contain rule preconditions and `_apply_*` functions
   perform immutable state transitions.
3. `distributed_simulations/algorithms/echo_execution.py` chooses queued
   message identifiers and records execution traces. It contains no Echo rule
   branches.
4. `distributed_simulations/protocol_compiled_runtime.py` implements generic
   operations such as reading a local field, replacing a field, removing the
   delivered message, and appending emitted messages.

The first two files are enough for understanding the algorithm. Read the
execution adapter for scheduling and tracing, and the runtime only when you
want details of the immutable data representation.

## The execution path

For each simulation run:

1. `echo.run_echo` converts the public topology into a formal configuration.
2. The generated startup rule sends a `request` message to every neighbor of
   the initiator.
3. The Python scheduler chooses the identifier of one queued message. It does
   not decide what that message means or how a node reacts.
4. Generated `step` resolves that identifier to the queued message, evaluates
   every rule guard, and requires exactly one enabled rule.
5. The selected generated action returns a new immutable state.
6. The runner repeats until the generated completion predicate succeeds, the
   state is stuck, or the delivery bound is reached.

This separation is intentional: scheduling chooses *which existing message is
delivered next*; the generated Rocq-derived functions decide *what delivery
does*.

## Where request reception lives

The first request received by a non-initiator matches one of two generated
rules:

- `first-request-nonleaf` when neighbors other than the sender remain;
- `first-request-leaf` when the sender is the only neighbor.

The non-leaf check establishes that the receiver is not the initiator, has not
already chosen a parent, has no pending children, is not finished, and has at
least one forwarding target.

Its generated action then performs the Echo logic directly:

```python
parent_node = receiver
parent_value = sender
state = _set_local_parent(state, parent_node, parent_value)

pending_node = receiver
pending_value = runtime.remove_first(sender, config.neighbors_of(receiver))
state = _set_local_pending(state, pending_node, pending_value)

state = runtime.remove_selected_message(state, event)
message_receivers = forwarding_targets
state = runtime.emit_many(
    state,
    "request",
    receiver,
    message_receivers,
    (),
)
```

The exact formatting is generated, but the important operations are visible:
the sender becomes the parent, all other neighbors become pending children,
the delivered message disappears, and requests are sent to those children.

The leaf rule chooses the sender as parent, marks the node finished, removes
the request, and immediately emits a reply to the parent.

## The nine generated rules

The executable contains these protocol cases:

| Rule | Meaning |
| --- | --- |
| `start` | The initiator sends requests to its neighbors. |
| `first-request-nonleaf` | A new participant chooses a parent and forwards requests. |
| `first-request-leaf` | A new leaf chooses a parent and immediately replies. |
| `repeated-request` | An already discovered participant rejects a later request with a reply. |
| `initiator-request` | The initiator replies to a request that returns to it. |
| `participant-reply-more` | A participant records a reply but still waits for others. |
| `participant-reply-final` | A participant receives its final reply and replies to its parent. |
| `initiator-reply-more` | The initiator records a reply and continues waiting. |
| `initiator-reply-final` | The initiator receives its final reply and completes. |

## What is generated and what is handwritten

Generated from the Rocq program:

- field declarations and initial state;
- completion and stuck predicates;
- every rule guard;
- every rule action;
- unique-rule dispatch;
- the Rocq program digest embedded in the executable.

Handwritten Python:

- topology and trace conversion;
- random selection of a queued message identifier;
- immutable runtime primitives shared by generated protocols;
- logging, exploration, and result formatting;
- tests that compare generated execution with Rocq fixtures and the retained
  interpreter oracle.

The handwritten runner must not contain alternate Echo branches. Otherwise a
Rocq change could leave a second Python model out of sync.

## Changing Echo

Change the Echo rule program in the sibling Rocq repository, rebuild it, and
then run:

```console
python3 tools/generate_echo_program_from_rocq.py
python3 tools/generate_echo_program_from_rocq.py --check
python3 -m unittest discover -v
```

If only the appearance of generated Python should change, edit
`tools/protocol_ir_python_compiler.py`, regenerate, and run the same tests.
Never hand-edit `generated_echo_executable.py`.

For certificate-free protocols such as Echo, generated callers can use the
small conveniences `start_event()` and `deliver(message_id)`. The lower-level
`make_*` constructors remain available for protocols with typed event fields.

## Migration-only files

`generated_echo_program.py`, `echo_ir_adapter.py`, and the oracle modules live
under `distributed_simulations/migration/`. They provide independent
conformance and migration checks and are not on the production Echo execution
path. The normal generator above never reads or writes them. Refresh the
serialized program only for an explicit comparison with
`python3 tools/generate_echo_migration_data_from_rocq.py`, normally through
the root `make regenerate-migration` target. Shared immutable data is defined
in `protocol_values.py`; typed syntax,
export codecs, and reference interpretation are separated into
`protocol_ir_ast.py`, `protocol_ir_codec.py`, and
`protocol_ir_interpreter.py`. `protocol_ir.py` is only a compatibility
re-export facade for previously documented imports.

## Public Python API

Application code should normally import `EchoNetwork` and `run_echo` from
`distributed_simulations.echo`, not import the generated module directly. The
public facade provides edge-list, adjacency-map, and JSON constructors; typed
results; FIFO, LIFO, and seeded-random delivery policies; in-memory traces;
and event callbacks. It contains no Echo guards or transition actions. Every
state change still passes through `generated_echo_executable.py`.
