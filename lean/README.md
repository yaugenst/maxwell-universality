# Lean formalization

The formalization develops the common sparse-system reduction, continuum
Maxwell analysis, discrete Yee operators, exact spectral certificates, and
finite computation and representation bounds. The pinned toolchain is in
`lean-toolchain`; `lake-manifest.json` fixes the dependency revisions.

[`proof-map.md`](proof-map.md) connects manuscript labels to selected Lean
declarations. [`proof-scopes.json`](proof-scopes.json) groups the existing
entry points into common, continuum, and discrete scopes. Module paths remain
under `Maxwell/`, so shared proofs have one implementation and both physical
models can import them directly.

| Location | Contents |
| --- | --- |
| `Maxwell/Algebra.lean`, `Interfaces.lean`, `Complexity.lean` | Finite identities and input, material, and exponent conventions |
| `Maxwell/Logical/`, `Composition/`, `Cost/`, `Codec/` | Sparse reduction, assembly, finite programs, and encoding |
| `Maxwell/Continuum/` | Continuum operators, spectral analysis, parameter choices, source/readout representation, and program constructions |
| `Maxwell/Target*.lean`, `Spectral/`, `Green/`, `Defect/` | Yee operators and discrete spectral and local-response ingredients |
| `Maxwell/Certificate/` | Exact arithmetic and spectral certificate proofs |
| `*Audit.lean`, `verify*.py` | Theorem inventories and verification entry points |
| `generate*.py`, `compile*.py`, `evidence/` | Certificate generation, recorded inputs, and verification receipts |

## Source and verification coverage

The recorded continuum audit passed 4,679 checks and inventoried 17,889
theorem declarations, including generated and private declarations, across
3,332 imported modules. It rebuilt that closure, audited axioms, replayed
1,344 continuum/audit modules individually, and checked the exported
theorems with their transitive proof/type dependencies from an empty
environment using the pinned Lean kernel. Its scope is the imported
components, not the complete uniform continuum reduction.

The source collection also includes later program constructions. Four
modules in the recorded closure were subsequently revised:
`CalibrationPowerInitialized`, `CalibrationNeumannInitialized`,
`CalibrationNeumannSetup`, and `CalibrationNeumannCopied`, all under
`Maxwell/Continuum/`. A [follow-up check](checks/continuum-refresh.json)
rebuilt these four modules and their three affected importers, replayed all
seven individually, and checked the complete refreshed export from an empty
environment. It passed for 17,906 theorem declarations, with all 3,337
recorded source/configuration hashes unchanged before and after the check.
Unchanged project modules came from the earlier audit's compiled cache;
this was an incremental rebuild with a complete export replay.

Three additional preserved modules have
unfinished validation: `WellAxisArithmetic` has a failed proof check, and
`WellSourceReadOne` and `SourceRoutingPathCounter` have not been compiled.
These three modules are outside the continuum audit closure.

To inspect the current import graph and compare it with the recorded hashes,
run from the repository root:

```bash
uv run --script lean/report_scope.py continuum
```

Omit `continuum` to report all three scopes. This command reads the sources,
receipt, and distribution manifest without compiling. It reports exact
matches, changed or missing files, and documented distribution transformations
separately. `data/manifest.json` remains the inventory of distributed bytes;
a matching source hash is evidence about the recorded run, not a new replay.

## Reproducing checks

Install Lean through elan, with `lake` on `PATH`. From the repository root,
install generated proof sources and recorded evidence:

```bash
uv run --script scripts/assets.py install --groups lean-generated lean-evidence
```

The common finite scope is the default build. From `lean/`:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

`Maxwell.lean` imports `Algebra`, `Complexity`, and `Interfaces`. The default
build therefore checks this finite scope. The continuum verifier has its own
root and build directory:

```bash
uv run --script verify_continuum_analysis.py
```

It checks dependency revisions and source hashes as well as compilation,
axiom inventories, and kernel replay. Accepted logical axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Its receipt and logs are
written to `evidence/continuum-analysis/`, replacing the recorded receipt that
the `lean-evidence` archive restores there. To compare a fresh run with the
recorded one, copy that directory first; `assets.py verify --groups
lean-evidence` reports the replaced files afterwards.

The verifier runs one compiler at a time with a 6,000 MB Lean memory limit
and at most two CPU cores where affinity is available. Plan for at least
8 GiB RAM and 20 GiB of working disk space beyond the downloaded archives;
no GPU is required. The recorded full audit took about 3.64 hours. Its local
dependency cache, scoped build, and proof export occupied approximately
7.5, 2.1, and 1.2 GiB respectively. Runtime and storage depend on the toolchain
cache and the selected closure.

The discrete entry points in `proof-scopes.json` select the stencil and
platform/instance components. Their declared hypotheses and audit output
determine the scope. Full certificate regeneration additionally needs the
`yee-witnesses` and `yee-receipts` asset groups.

`verify.py` is the whole-development gate for the final discrete theorem
`Maxwell.Realization.quantitative_realization`. That theorem is not yet stated
in this snapshot, so the gate does not pass. It requires every project source
to be reachable from `Maxwell.lean` and checks the theorem's exact type; the
current default root also does not meet that import-closure requirement.
A complete continuum realization also needs its own final theorem and type
check; the component scope reports do not supply that conclusion.

## Distribution

Lean source text is preserved unchanged. Python helpers resolve the relocated
`certificates/yee/` inputs and locate `lake` on `PATH`. Published execution
metadata omits host identifiers and replaces local paths; numerical values,
software versions, and reported scopes are retained. The manifest records
original and distributed hashes for transformed files. Build caches,
compiler logs, and regenerable proof exports are omitted from the release.
See [`docs/snapshot.md`](../docs/snapshot.md) for the complete artifact inventory.
