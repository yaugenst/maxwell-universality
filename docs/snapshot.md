# Artifact snapshot: 29 October 2026

This is a curated artifact snapshot for
[`yaugenst/maxwell-universality`](https://github.com/yaugenst/maxwell-universality).
The Lean source snapshot began at 16:09:52 UTC. Core source additions were
captured through 16:32:45 UTC; archived audit receipts retain their original
timestamps and verification scopes. The manuscript sources incorporate later
literature revisions.

## Included material

The import manifest accounts for 45,689 files. Of these, 4,370 files (about
63 MiB) are shipped directly in Git; the rest are in 22 companion archives
(about 5.79 GiB compressed). The repository also contains its new guides and
archive utility.

All 36,188 Lean source files in the snapshot are preserved: 2,998 directly in
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
logs, duplicate replay snapshots, and the regenerable 624 MB proof export are
excluded. The Lean reproduction entry points are in `lean/README.md`.

## Checks performed on this package

- Installed every archive and verified all 45,689 imported files against their
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
Yee replay, large three-dimensional solves, and complete formal reduction were
not rerun as part of this import. The archived continuum audit receipt records
`running`, with 470 modules and 942 checks at capture time. It is a snapshot of
that separate process, not a completed verification claim. `verify.py` still
requires a whole-development import closure absent from this snapshot.

The document build requires a complete TeX Live installation. The
interval-kernel replay requires a C++ compiler with its matching UBSan runtime.
