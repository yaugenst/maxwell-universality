# Reproducing the companion artifact

Commands below start in the repository root. Use new output directories so a
fresh run remains distinguishable from a recorded result.

## Choose the work you want to reproduce

| Task | Extra data | Compute |
| --- | --- | --- |
| Read reports and open exported walkthroughs | None | Browser |
| Build manuscript and redraw paper figures | None | LaTeX; Python, NumPy, Matplotlib |
| Build the arXiv source ZIP and check its extracted contents | None | Git; Python standard library; LaTeX and BibTeX |
| Recompute continuum finite algebra | None | Python standard library |
| Calibrate the waveguide and rerun its precision study | None | CPU, NumPy, SciPy |
| Reconstruct figures and readouts from saved full-vector fields | `demo-fields` | CPU and a few GB of memory |
| Inspect all generated Lean sources | `lean-generated`, `lean-evidence` | Disk space |
| Replay discrete computational premises | `yee-witnesses` | CPU, NumPy, C++17 compiler |
| Regenerate discrete Lean witness material | `lean-evidence`, `yee-witnesses`, `yee-receipts` | Depends on the generator and compilation scope |
| Inspect all numerical fields and rerun the periodic studies | `numerical-fields`, `demo-fields` | Large sparse direct solves may require a high-memory GPU |

See the [paper](../paper/README.md), [Lean](../lean/README.md),
[certificate](../certificates/README.md), and
[experiment](../experiments/README.md) guides for the commands and scopes.

## Companion archives

The archives accompany the `artifact-2026-10-29` release in
[`yaugenst/maxwell-universality`](https://github.com/yaugenst/maxwell-universality).
During preparation, the repository is private and the release is a draft.
Use an account with access to download them:

```bash
gh release download artifact-2026-10-29 --repo yaugenst/maxwell-universality \
  --dir .release-assets --pattern '*.tar.gz'
```

For a smaller download, replace the pattern with a group prefix such as
`'demo-fields-*.tar.gz'` or `'lean-generated-*.tar.gz'`.

List the groups and compressed sizes:

```bash
uv run --script scripts/assets.py list
```

Place the desired archives in `.release-assets/`, or point to another directory:

```bash
uv run --script scripts/assets.py install --groups demo-fields \
  --asset-dir /path/to/downloads
uv run --script scripts/assets.py verify --groups core demo-fields
```

For the complete imported artifact:

```bash
uv run --script scripts/assets.py install
uv run --script scripts/assets.py verify --all
```

The installer checks each archive and member against `data/manifest.json`,
restores repository-relative paths, and refuses to overwrite a changed file.
Matching existing files are retained, so installation can be repeated. Allow
space for both compressed archives and their extracted contents. Large files
stay outside Git; their checksums and paths are tracked.

`verify` checks the imported snapshot. If you intentionally edit source or
regenerate outputs, it reports those changes; it is not a test of the new
mathematics or numerical result. A future release should update the manifest
when adopting a new snapshot.

## Reproducibility records

The [snapshot note](snapshot.md) records which files were imported and which
checks were rerun during packaging. New computational receipts go under
`build/`; the exact Yee runner also creates a source snapshot for each run.
The original recorded receipts remain separately labeled.

The Python scripts contain their dependency ranges in inline metadata where
available. The GPU experiments additionally preserve the installed package
versions. Lean and mathlib use explicit revision pins. LaTeX output is a
typesetting check; it does not execute the proof audits or certificate replay.
