# Lean development

This directory preserves the formal sources from the research snapshot,
including the continuum analysis, discrete spectral and certificate work,
logical composition, cost estimates, and experimental witness bindings.
The pinned Lean toolchain is in `lean-toolchain`; dependency revisions are in
`lake-manifest.json`.

## Layout

| Location | Contents |
| --- | --- |
| `Maxwell/Continuum/` | Continuum analytic components |
| `Maxwell/Certificate/` | Exact-arithmetic infrastructure and witness bindings |
| `Maxwell/Spectral/`, `Green/`, `Defect/` | Spectral and local-response ingredients |
| `Maxwell/Logical/`, `Composition/`, `Cost/`, `Realization/` | Reduction interfaces, composition, and resource bounds |
| `*Audit.lean`, `verify*.py` | Audit entry points with different scopes |
| `generate*.py`, `compile*.py` | Witness generation and compilation tools |

Generated witness modules are kept in the `lean-generated` archives. Install
them before working on the full source tree:

```bash
uv run --script scripts/assets.py install --groups lean-generated
```

The manifest accounts for every `.lean` source in the snapshot, including
sources under `evidence/`, which are in `lean-evidence`. Build caches, compiler
logs, and the large regenerable proof export are omitted. To regenerate witnesses
from their recorded inputs, also install `lean-evidence`, `yee-witnesses`, and
`yee-receipts`.

## Checking a stated scope

Install Lean through elan, with `lake` on `PATH`. From `lean/`:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

The default `Maxwell.lean` imports `Algebra`, `Complexity`, and `Interfaces`.
Consequently, the default build and `Audit.lean` cover that finite interface,
not every directory listed above. The audit enumerates the imported theorems
and the axioms they use.

For the continuum analytic closure, the separate entry point is:

```bash
uv run --script verify_continuum_analysis.py
```

It compiles the transitive closure of `ContinuumAnalysisAudit.lean`, checks
dependency revisions and source hashes, audits axioms, and replays proof
exports. Its stated scope is “imported continuum analytic components; not the
complete Maxwell reduction.” Allow substantial runtime and disk space; this is
not part of the small numerical quickstart.

`verify.py` is the stricter whole-development gate. It requires every project
source to be reachable from `Maxwell.lean` and checks for the final quantitative
realization theorem. That import-closure requirement is not met in this snapshot.
Shipping these sources does not change that status. See
[`docs/snapshot.md`](../docs/snapshot.md) for the captured state and packaging
checks.

## Reproducibility details

The `.lean` text is copied unchanged. Python helpers locate the relocated
`certificates/yee/` inputs and `lake` on `PATH`. Published execution metadata
omits host identifiers and generalizes local paths; numerical values, software
versions and reported scopes are retained. The manifest records original and
distributed hashes for changed files. Frozen certificate verifier sources
retain their original bytes. Digests inside historical receipts describe the
original execution; rerun an audit to obtain a receipt for this checkout.

The development contains research and prototype entry points beyond the two
commands above. Their inclusion preserves the work; it does not assert that
every prototype is a completed proof or a supported standalone build target.
