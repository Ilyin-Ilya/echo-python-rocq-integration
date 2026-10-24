# Distributed Simulations

This repository runs message-passing algorithms in one Python process. A seeded
scheduler chooses one pending message at each step, which makes delivery orders
controllable without adding threads or network timing.

The maintained implementations are:

- Echo spanning-tree construction
- Dijkstra-Scholten termination detection
- Lai-Yang-style snapshot collection
- Bracha-Toueg deadlock detection over a collected wait-for relation

The handwritten implementations use `distributed_simulations/runtime.py`.
Echo instead uses a small immutable runtime plus Python transition functions
generated from its proved Rocq program. Algorithm entry points are under
`distributed_simulations/algorithms/`, and runnable topologies are under
`examples/`.

## Install

Install the package from this directory with:

```console
python3 -m pip install .
```

The wheel contains the production generated Echo executable and its required
runtime, but excludes the serialized migration implementation and test-only
oracles.

## Run

Python 3.9 or newer is required. There are no runtime dependencies.

```console
python3 main.py echo --seed 0 --log execution_log.jsonl
python3 main.py dijkstra-scholten --seed 0
python3 main.py lai-yang --seed 0
python3 main.py bracha-toueg --seed 0
```

Echo always uses the transition core generated from the proved Rocq model.

Use `--graph PATH` for another topology and `--max-steps N` to bound a run. The
command prints a JSON result containing the run outcome, delivery count,
verification status, and algorithm-specific details. Logs use JSON Lines and
include unique message IDs and delivery steps.

## Use from Python

The public API accepts a validated network and returns a typed Echo result:

```python
from distributed_simulations.echo import EchoNetwork, run_echo

network = EchoNetwork.from_edges(
    [("A", "B"), ("B", "C"), ("A", "C")],
    initiator="A",
)
result = run_echo(network, scheduler="fifo")

print(result.completed)  # True
print(result.parents)    # parent selected for every non-initiator
print(result.verified)   # runtime tree check plus documented proof scope
print(result.path_to_initiator("C"))
print(result.tree_edges)
```

For a small script, an adjacency map can be passed directly when the
initiator is explicit:

```python
result = run_echo(
    {"A": ["B"], "B": ["A"]},
    initiator="A",
)
```

`EchoNetwork.from_adjacency(...)` accepts an adjacency mapping, while
`EchoNetwork.from_json(...)` accepts the existing example format. The
available protocol-neutral delivery policies are `"random"`, `"fifo"`, and
`"lifo"`. Random delivery is reproducible through `seed`. A custom scheduler
may inspect the immutable tuple of pending-message descriptions and return one
of their `message_id` values; it cannot provide a successor state.

The result also exposes `parent_of(node)`, `children_of(node)`,
`path_to_initiator(node)`, and `tree_edges`. For a bounded run that has not
discovered a complete path, `path_to_initiator` returns `None`.

Capture a trace in memory or observe events as they happen without changing
the generated transition behavior:

```python
result = run_echo(network, capture_trace=True)
print(result.trace)

run_echo(network, on_event=lambda event: print(event["event"]))
```

The lower-level `distributed_simulations.algorithms.run_echo` entry point is
kept for compatibility with the other simulations. New Python integrations
should use `distributed_simulations.echo` or the package-level exports.

Echo logs additionally use the versioned
`distributed-simulations.echo/v3` schema. They contain a topology digest, the
exact Rocq program and evaluation-vector digests, and a canonical snapshot
after startup and after every delivery. Replay one through the same generated
transition semantics:

```console
python3 -m distributed_simulations.algorithms.echo_trace execution_log.jsonl
```

The checker exits at the first mismatching event and verifies topology
assumptions, message-ID selection, state updates, emitted messages, and the
guards exported from Rocq.

To enumerate every pending-message choice up to explicit bounds, run:

```console
python3 -m distributed_simulations.algorithms.echo_explorer \
  examples/echo.json --max-depth 20 --max-states 100000
```

The explorer uses breadth-first search, hashes states after erasing runtime-only
message IDs, eliminates duplicates, checks transferred parent/message/decision
properties, and returns the shortest delivery-ID path to any violation.

Use `--mutation` to run the same BFS against one of the controlled faulty
handlers: `early-root-finish`, `wrong-parent`, `drop-pending-removal`,
`duplicate-ack-emission`, or `post-decision-echo`. The command exits nonzero
and prints the shortest triggering schedule when the mutation diverges from
the generated Echo transition.

Generate the reproducible topology/mutation report with:

```console
python3 -m distributed_simulations.algorithms.echo_evaluation \
  --output ECHO_EXPLORATION_REPORT.md
```

## Rocq-generated Echo executable

The authoritative Echo guard/action program is `echo_ir_program` in the
sibling Rocq project. The normal generator produces one artifact:

- `generated_echo_executable.py` is the production Python implementation. It
  contains ordinary generated functions for guards and state transitions.
After changing the Rocq program, regenerate the production artifact with:

```console
python3 tools/generate_echo_program_from_rocq.py
python3 tools/generate_echo_program_from_rocq.py --check
```

The optional migration workflow separately owns
`distributed_simulations/migration/generated_echo_program.py`, the serialized
IR retained for interpreter and conformance comparisons. Refresh it with
`python3 tools/generate_echo_migration_data_from_rocq.py`, normally through the
root `make regenerate-migration` target. Production generation, packaging, and
execution do not require this file.

Normal simulation imports `generated_echo_executable.py`; it does not need
Rocq or OCaml at runtime. A seeded scheduler selects only a queued message ID.
The generated `step` function checks every generated rule, requires exactly
one to be enabled, and calls that rule's generated action to construct the
successor state.

`distributed_simulations/algorithms/echo_codec.py` is the maintained conversion
boundary for topology and trace values. It contains no Echo transition rules.
`distributed_simulations/algorithms/echo_execution.py` contains scheduling and
trace observation, also without protocol rule branches.
The generic immutable operations used by generated code live in
`distributed_simulations/protocol_compiled_runtime.py`.

For a Python-oriented tour, including the request-receiving and parent-setting
path, read [`ECHO_CODE_GUIDE.md`](ECHO_CODE_GUIDE.md).

A singleton graph completes through the same generated executable and formal
program as every other connected topology.

New Echo protocol changes begin in Rocq, followed by regeneration and the test
suite. Handwritten Python retains only protocol-neutral runtime operations,
topology/trace conversion, scheduling, logging, and result presentation. The
serialized program, generic interpreter, and older generated oracle remain for
cross-model tests; production execution and replay do not import them.

## Topology

Each role lists its neighbors separately. Algorithms in this repository expect
a connected, symmetric graph and exactly one role marked as the initiator.
Snapshot and deadlock examples may also provide a `requests` list.

```json
{
  "A": {"role": "initiator", "neighbors": ["B", "D"]},
  "B": {"role": "participant", "neighbors": ["A", "C"]},
  "C": {"role": "participant", "neighbors": ["B", "D"]},
  "D": {"role": "participant", "neighbors": ["A", "C"]}
}
```

## Test

```console
python3 -m unittest discover -v
```

The tests exercise cyclic topologies, several random schedules, bounded runs,
snapshot collection, deadlock detection, topology validation, valid Echo trace
replay, and first-mismatch reporting for a mutated trace.
