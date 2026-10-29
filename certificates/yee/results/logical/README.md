# Logical reduction

This directory contains the R5 logical reduction and its exact-arithmetic
implementation checks. Its analytic statements concern the logical network;
the physical Maxwell construction has separate hypotheses.

## Files

- `r5_constructive_proof.md`: all-input analytic construction and bounds.
- `kwz_transfer.md`: independently derived rectangular Real-RAM transfer,
  short dyadic rounding, verification, and conditional SLTH scope.
- `verify_logical.py`: Python 3 exact-arithmetic implementation checks.
- `verification_log.json`: a freshly generated check log, including runtime
  version, deterministic seed, counts, and the checker source hash.
- `verify_h2_scalar_bounds.py` and `h2_scalar_verification.json`: exact
  arithmetic checks of the scalar constants in the analytic H2 construction.

## Reproduce the implementation checks

From a clean copy of this directory, run:

```sh
python3 verify_logical.py > regenerated_verification_log.json
```

Only the Python standard library is used. Do not use `python -O`: assertions
are part of the checker. The command recomputes the checks; it never reads
or accepts the saved log. It takes seconds on the tested Python 3.12
runtime. The log's runtime string may differ on another
machine; the exact combinatorial quantities are deterministic.

The checks cover two rational arithmetic circuits, every four-token
permutation on the 2-by-2 mesh, additional seeded permutations on the
4-by-4 and 8-by-8 meshes, 24 seeded bipartite degree-three graphs, the exact
swap-gadget geometry, and zero-diagonal path inverses through 64 internal
vertices. All computations use integers or rational `Fraction` values.

These finite checks validate the implementation on those cases. The
all-size routing, conditioning, residual, and complexity assertions are
proved analytically in the two Markdown documents. They are not inferred
from the finite checks and have not been formalized in a proof assistant.
