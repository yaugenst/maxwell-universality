# Numerical figure inputs

`numerical_illustrations.json` and `numerical_illustrations.npz` contain the
archived measurements and reduced field sections for `fig_numerical.pdf` and
`si/numerical_controls.pdf`. The source-file SHA-256 hashes are stored under
`provenance.files_sha256` in the JSON. All paths there are relative to the
numerical experiment directory (`experiments/` in the companion repository).

Figure regeneration uses a CPU and 64-bit floating-point arrays. It needs no
GPU or Maxwell solver. A one-thread replay used 107 MiB of peak host memory;
512 MiB is a suggested allocation for this figure-only workflow. The bundled
plotting inputs occupy about 200 KB; the large field arrays are needed only
for optional re-extraction.

From the paper directory:

```bash
uv run --script figures/fig_numerical.py
```

This also regenerates `waveguide_errors.tex`, the supplementary refinement
table. It performs no optimization or Maxwell solve. The target solution in
the readout panels is calculated only as a comparison to the measured answer.

To reconstruct the figure inputs from the full experiment archive:

```bash
uv run --script figures/fig_numerical.py --refresh-data \
  --experiment-root ../experiments
```

During extraction, the script reconstructs each displayed response from the
original full-grid fields and probes and verifies the source programming and
reported equation error. The periodic field section is interpolated from the
staggered vector grid to cell centers and then to `y=0`. The waveguide curve
uses the saved `Ey` centerline. Spatial interpolation and display normalization
never enter the decoded responses or the error table.

The full-vector simulations used a GPU direct solver, 64-bit arithmetic,
two host numerical-library threads and one concurrent job per GPU. The
factorization plan for the 379,610-unknown periodic case estimated
112,605,351,652 bytes (112.6 GB) of peak device memory. This is a plan estimate
for that matrix and backend, not a measured peak or a minimum requirement for
other solvers. Local component calibration runs on the CPU. Backend versions,
timings, factor sizes and numerical measurements are retained in the data;
hostnames and machine identities are omitted.

These inputs record numerical examples and refinement checks. The separate
proof-checking artifacts are described in Part V of the supplementary
information.
