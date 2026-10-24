# Rocq-to-Python bridge artifacts

`rocq_echo_program.sexp` is the canonical value obtained by asking Rocq to
evaluate `echo_program_sexpr`. It contains the real nine-rule guard/action
program, not only branch labels. `rocq_echo_vectors.sexp` contains ten concrete
input/result vectors computed by Rocq itself: all nine successful operations
plus one rejected certificate. `rocq_echo_run_vectors.sexp` contains seven
complete-run results covering successful schedules, alternate delivery order,
singleton completion, stuck, bounded, and invalid-choice outcomes.
`distributed_simulations/migration/generated_echo_oracles.py` is
deterministically rendered from all three values. It contains literal data
only: no transition function, runner, class, or import.

From the integration root, regenerate the optional migration artifacts with:

```console
make regenerate-migration
```

Use `make compare` to build the isolated migration project and check freshness.
It fails if any historical export or the generated Python file is missing,
stale, or manually edited. The comparison suite executes every Rocq-computed
single-step and full-run vector using the shared generic interpreter and the
generated generic Echo program.

The production entry point always executes the generated Python functions:

```python
result = run_echo(topology, seed=7)
```

`run_echo` validates and converts the topology, supplies a seeded callback that
selects one queued message identifier, and observes immutable states for
logging. `generated_echo_executable.py` owns the protocol-specific transition
functions. The serialized program and oracle modules under
`distributed_simulations/migration/` are never imported by production.

The former Python-AST-to-Rocq manifest was a migration aid. It was removed once
the Rocq-to-Python path became authoritative. These oracle artifacts now have
one optional migration-only freshness gate: `make compare`.
