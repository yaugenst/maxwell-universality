# Artifact snapshot: 30 October 2026

This is a curated artifact snapshot for
[`yaugenst/maxwell-universality`](https://github.com/yaugenst/maxwell-universality).
The numerical and discrete certificate data were captured on 29 October.
The complete Lean source collection was updated on 30 October at 09:37:42 UTC;
archived audit receipts retain their original verification scopes. The
manuscript incorporates the corresponding corrections to constants,
calibration, finite representation, and computational costs.

## Included material

The artifact manifest accounts for 47,372 files. Of these, 6,047 files (about
75 MiB) are shipped directly in Git; the rest are in 22 companion archives
(about 5.79 GiB compressed). The repository also contains its new guides and
archive utility.

All 37,864 Lean source files in the snapshot are preserved: 4,674 directly in
Git, 32,945 generated certificate modules in `lean-generated`, and 245 under
the archived evidence directories. Every local `Maxwell` import resolves to a
source file in the installed snapshot. Generated source text is unchanged.
Python helpers have portability edits for relocated inputs and executables.
Published metadata omits machine identities and local device assignments,
and generalizes execution paths. CPU/GPU backends, software versions,
numerical values, timing and memory records are retained. The manifest records
original and distributed hashes for changed files; digests inside historical
receipts continue to describe the original recorded execution.

The numerical archive includes successful and unsuccessful studies, frozen
designs, intermediate measurements, executed-source copies, and full fields.
The exact Yee input set is selected by the original replay controller and
checked against its frozen manifests. Stored receipts from the independent
reference replay are kept separately from fresh outputs.

The package contains manuscript sources, proofs, code, data, figures, and
reproduction documentation. Dependency caches, compiled Lean objects, compiler
logs, duplicate replay snapshots, and regenerable proof exports are excluded.
The Lean reproduction entry points are in `lean/README.md`. The
[proof map](../lean/proof-map.md) connects manuscript statements to formal
declarations, and `lean/proof-scopes.json` identifies the shared, continuum,
and discrete entry points without changing their module paths.

## Checks performed on this package

- Installed every archive and verified the imported files against their
  SHA-256 hashes, including all generated Lean sources.
- Replayed the continuum finite rational checker successfully.
- Replayed the Yee logical, composition, scalar, defect-geometry, PEC, interval
  kernel, and H1 geometry groups. The controller reports
  `ESTABLISHED_CHECKS_PASSED_NOT_FULL`, as required for this partial run.
- Recomputed the waveguide calibration. Its local eigenvalue, coupling, and
  confinement fraction matched the archived values exactly. Recomputed the
  70-case spacing/rounding study at channel spacing 0.0025.
- Regenerated the periodic and waveguide figures from archived full-vector
  fields. Their source/decoder identities and quantitative readouts passed the
  visualizers' checks.
- Regenerated both paper numerical figures and the refinement table using
  only the compact bundled data. Built the manuscript with no overfull boxes,
  undefined references, or duplicate labels.
- Freshly compiled `Algebra`, `Complexity`, `Interfaces`, and the `Maxwell`
  root, then ran `Audit.lean`. It enumerated 67 theorems, no project-declared
  axioms, and only `propext`, `Classical.choice`, and `Quot.sound` in theorem
  dependencies. This check reused the existing pinned mathlib dependency
  cache, with fresh local proof objects.

These are packaging and scoped reproduction checks. The full multi-gigabyte
Yee replay and large three-dimensional solves were not repeated for this
source update.

The archived continuum audit records a successful 4,679-check run over 3,332
modules, with 17,889 theorem declarations and a proof-dependency replay from
an empty environment. The run took about 3.64 hours; its proof export was about
1.15 GiB. These are observations from that run, rather than resource bounds.
Four calibration modules changed after it. The
[refreshed receipt](../lean/checks/continuum-refresh.json) records successful
strict recompilation and individual kernel replay of the seven affected
modules, followed by a complete export replay of 17,906 theorem declarations
from an empty environment. Unchanged compiled modules came from the prior
audit cache. All 3,337 source and configuration hashes matched before and
after checking. This refresh took about nine minutes; it did not rebuild the
entire source closure.

The refreshed root includes 1,343 of the 2,276 continuum modules; later encoder
components extend beyond it. `lean/report_scope.py` compares each receipt's
source hashes and module inventory with the installed files. The historical
receipt reports its four changed sources; the refreshed receipt matches the
current audit closure.

The collection preserves three unfinished source leaves:
`SourceRoutingPathCounter`, `WellSourceReadOne`, and `WellAxisArithmetic` under
`Maxwell/Continuum/`. The first two had no completed check at capture; the last
had a failed check of `output_value`. They are outside the continuum audit
root. The complete finite encoder still requires composition of its checked
components and an integrated audit. The stricter `verify.py` gate requires a
whole-development import closure and final realization theorem; this source
collection does not claim that gate has passed.

The document build requires a complete TeX Live installation. The
interval-kernel replay requires a C++ compiler with its matching UBSan runtime.
