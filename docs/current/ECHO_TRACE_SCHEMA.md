# Echo execution trace schema

Schema identifier: `distributed-simulations.echo/v3`

The trace is UTF-8 JSON Lines. Each non-empty line is one JSON object. Numeric
message identifiers are allocated consecutively from 1 and are never reused.

## Header

The first record has `event: "trace_header"` and contains:

- `schema` and `algorithm` (`echo`);
- canonical topology: one initiator and each node's ordered neighbor list;
- `topology_sha256`, computed from compact, key-sorted topology JSON;
- scheduler `seed` and `max_steps`;
- `python_version`;
- `code_revision` (installed package version or `source-tree`);
- `rocq_program_sha256`, the exact serialized generic Rocq IR program loaded
  by Python;
- `rocq_ir_schema_version`, the export-envelope version; and
- `rocq_ir_version`, the generic instruction-set version.

The ordered neighbor list is retained because it determines startup message-ID
allocation. The formal refinement treats the corresponding packet collection
up to permutation.

## Runtime events

Existing `enqueue`, `deliver`, `tree_edge`, and `run_finished` records remain
in the stream. A `deliver` record identifies the selected envelope by its
unique `message_id` and repeats its kind, sender, receiver, and payload.

## Canonical snapshots

A snapshot occurs immediately after startup and after every delivery. It has:

```json
{
  "event": "snapshot",
  "step": 0,
  "point": "after_start",
  "state": {
    "started": true,
    "roles": {
      "A": {"parent": null, "pending": ["B"], "finished": false}
    }
  },
  "store": [
    {"message_id": 1, "kind": "ECHO", "sender": "A", "receiver": "B", "payload": {}}
  ],
  "next_message_id": 2
}
```

`pending` is sorted in every role snapshot. `store` preserves scheduler queue
order. The initiator's `finished` field is derived as `started && !pending`;
participant `finished` fields are stored by the interpreted Rocq IR state.

## Checker contract

`distributed_simulations.algorithms.echo_trace` reconstructs startup and each
delivery with the same generated `generated_echo_executable.py` transition
functions used by production. It validates:

- schema, algorithm, topology digest, connectivity, symmetry, absence of
  self-edges, and duplicate-free neighbor lists;
- exact message-ID selection and envelope contents;
- role, pending-set, parent, completion, queue, emission, and next-ID updates;
- the initiator never has a parent; and
- no ECHO is delivered to the initiator after it has decided.

The checker stops at the first mismatch and reports its zero-based event index.
Successful output includes the checked transition count.

Run it with:

```console
python3 -m distributed_simulations.algorithms.echo_trace TRACE.jsonl
```

This v3 checker consumes the same generated executable as the complete runner.
The trace `deliver` record identifies the queued message, and the checker
compares the exact generated successor with the next snapshot. Echo events do
not carry certificates.

The checker rejects older schemas and v3 traces whose Rocq program digest or
IR versions do not match the generated artifact it loaded. It intentionally
reuses the generated transition implementation, so it checks scheduling,
serialization, and artifact identity but is not an independent implementation
of Echo.
