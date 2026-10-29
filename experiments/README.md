# Numerical illustrations

Two complementary demonstrations connect prescribed matrix coefficients to a
dielectric device and its measured response.

| Study | Design procedure | Evidence |
| --- | --- | --- |
| Periodic cavity | Fit one assembled device, then freeze its material, sources, and decoder for refinement. | A signed three-variable target reaches 0.0788% worst-case equation error on the finest tested grid. |
| Waveguide chains | Calibrate one isolated component, compute its pair coupling, and set each site's strength from the requested diagonal. | Five targets pass the 1% gate on both finer full-vector grids, without fitting the assembled response. |

The [periodic walkthrough](report/device_walkthrough/README.md) and
[waveguide walkthrough](report/local_compilation/walkthrough/README.md) explain
the geometry, input, field, and readout. Each directory contains a standalone
`preview.html`. Download or serve the repository locally to open these pages;
GitHub's file viewer displays their source.

The larger [periodic study](report/EXTENDED.md) includes the ill-conditioned
counterexample and unsuccessful refinement cases. The
[local-compilation report](report/local_compilation/README.md) includes failed
periodic assembly, five successful waveguide targets, boundary tests, and the
spacing/precision tradeoff. These reports preserve the measured limitations.

## CPU reproduction

Run from the repository root. Every solve writes to a new output directory:

```bash
uv run --script experiments/waveguide_control.py calibrate \
  --output build/waveguide-calibration
uv run --script experiments/waveguide_tradeoff.py \
  --reference build/waveguide-calibration \
  --output build/waveguide-tradeoff --spacing 0.0025
```

The calibration solves a one-dimensional isolated-component problem. The
tradeoff script solves the exact TE10 channel for different separations and
material rounding, while retaining the nominal source and decoder. This is a
small CPU reproduction of the design rule and precision argument. It is
separate from the full-vector three-dimensional checks.

To reconstruct the saved full-grid source/readout identities and regenerate the
walkthrough figures, install the `demo-fields` archive group:

```bash
uv run --script scripts/assets.py install --groups demo-fields
uv run --script experiments/visualize_device.py
uv run --script experiments/visualize_waveguide.py \
  --inline-output build/waveguide-walkthrough.html
uv run --script experiments/analyze_local.py
```

The visualizers read archived fields; they do not perform a new physical solve.
They recompute quantitative readouts on the original staggered grids before
creating reduced display data. `--inline-output` writes the interactive fragment;
the already bundled `report/**/preview.html` files are standalone exports.

## Full-vector Maxwell verification

The recorded large runs used GPU sparse direct factorization through cuDSS,
with 64-bit arithmetic, two host numerical-library threads and one job per GPU.
For the 379,610-unknown periodic case, the factorization plan estimated
112.6 GB peak device memory. This is a matrix- and backend-specific estimate,
not a measured peak or a minimum for other solvers. Reserve additional memory
for inputs and runtime overhead. The largest waveguide grid has 380,100 electric
unknowns; its factorization needs a separate memory plan. The CPU `direct`
backend supports smaller grids.

| Task | Processor | Memory guidance |
| --- | --- | --- |
| Redraw paper figures from compact data | CPU, one numerical-library thread | 107 MiB measured peak host RAM; allow 512 MiB |
| Recompute the isolated waveguide calibration | CPU, two numerical-library threads | 209 MiB measured peak host RAM; allow 512 MiB |
| Reconstruct walkthroughs from saved fields | CPU | Allow a few GB of host RAM |
| Repeat fine full-vector solves | GPU direct solver | Plan each factorization; the periodic example estimates 112.6 GB device memory before extra headroom |

The measured host-memory figures describe these reproduction commands, not
universal bounds. Sparse factorization fill depends on geometry and ordering;
matrix dimension alone does not determine its memory use.

The recorded CUDA/Python package versions are in
[`results/local_compilation/gpu_environment.txt`](results/local_compilation/gpu_environment.txt).
On a compatible CUDA 12 host, one way to create a separate environment is:

```bash
uv venv --python 3.12 build/cuda-env
uv pip install --python build/cuda-env/bin/python \
  -r experiments/results/local_compilation/gpu_environment.txt
```

Use one solve per GPU and limit host library threads. After the calibration above:

```bash
OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 \
  build/cuda-env/bin/python experiments/waveguide_control.py verify \
  --reference build/waveguide-calibration --name chain4 \
  --output build/waveguide-chain4 --solver cudss
```

Repeat with `chain3`, `nonuniform3`, and `mediator2`. For `indefinite3`, use
`--h 0.05 0.045454545454545456 0.041666666666666664`, matching the recorded
three-grid check. The larger-wall control uses `--name chain3 --buffer-extra 4
--h 0.05 0.045454545454545456`.

For the complete periodic research workflow, use the archived designs,
parameters, and executed-source copies in `results/`; install `numerical-fields`
as well. The top-level scripts provide the reusable implementations:

| Scripts | Role |
| --- | --- |
| `maxwell.py`, `device.py`, `network.py` | Staggered full-vector operator, sources, response, and assembled calibration |
| `refine_device.py`, `verify_candidates.py` | Frozen-design verification and refinement |
| `conditioning.py`, `precision.py`, `robustness.py`, `diagnose_modes.py` | Conditioning and sensitivity diagnostics |
| `local_library.py`, `local_transfer.py`, `local_compile.py` | Periodic component-calibration and assembly experiments |
| `waveguide_control.py`, `waveguide_tradeoff.py` | Reusable waveguide control and precision study |
| `analyze*.py`, `visualize*.py` | Reports, figures, and readout reconstruction |

Recorded results include the code that executed each case when available.
Those copies are provenance; the scripts at this directory's root are the
entry points for new runs. The results are physical and numerical demonstrations,
not solver-performance benchmarks or an implementation of the paper's full
asymptotic compiler.
