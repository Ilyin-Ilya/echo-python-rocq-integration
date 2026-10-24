# Mathematics of Arrays formalization

This directory contains a checked Rocq 9.0 core for Hains and Mullin,
“New Mathematics for Computer Performance: Array Algebra and Cost Functions”,
Mathematics 14(9), 1479 (2026), DOI: 10.3390/math14091479.

The formalization deliberately separates results supported by precise
definitions from the article's empirical performance claims.

## Modules

- `theories/MoAArray.v` defines well-formed shape/content arrays, row-major
  `gamma`, valid indices, flat lookup, ravel preservation, and the arithmetic
  decomposition underlying compositional `Psi` indexing.
- `theories/MoAReduction.v` proves the monoidal reduction split law.
- `theories/MoACost.v` gives structured sequential/parallel executions,
  includes instruction and transfer costs uniformly, and proves that a
  semantics-authorized dimension lifting cannot increase cost. It also checks
  the symbolic inequalities in Table 1.
- `theories/MoAExample.v` evaluates a concrete 2-by-3 array, reduction split,
  and sequential-to-parallel cost example inside Rocq.

All theorems end in `Qed`; the final audit uses `Print Assumptions`.

## Explicit repairs to the source specification

1. Definition 9's recursive map equation must map the tail. As printed, it is
   ill-typed when the source and target element types differ.
2. Proposition 4 uses `delta(v)`, but dimensionality is one for every vector.
   `reduction_split` uses `k <= length v`, corresponding to total size
   `tau(v)`. The source's strict variant follows immediately.
3. Proposition 2 is treated uniformly using total `option` lookup. Scalars use
   the empty full index; invalid or dimension-mismatched lookups return `None`.
4. Definition 25 mentions edge costs but omits them from its recurrence.
   `Work c` represents either an instruction or transfer, so neither is lost.
5. Definition 26 does not define a correspondence between transformed
   subgraphs. `dimension_lifting` is therefore structural and requires an
   explicit independence certificate before sequential work becomes parallel.
6. The cost theorem states the exact algebraic assumptions it needs:
   monotonicity of both combinators and `parallel <= sequential`.

## Scope boundary

The article does not supply a complete syntax, rewrite system, or normalization
algorithm for DNF and ONF. Consequently, this development does not claim a
verified general MoA compiler or prove empirical prediction accuracy. Those
require additional specifications: an expression AST, a loop language,
semantics for both, normalization rules, and a calibrated hardware model.

## Build

Use the repository's normal command. With the bundled macOS Rocq Platform:

```sh
make -j2 \
  COQBIN="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/bin" \
  ROCQLIB="/Applications/Rocq-Platform~9.0~2025.08.app/Contents/Resources/lib/coq"
```
