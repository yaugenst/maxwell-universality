# Exact computational certificates

Run these commands from the repository root. Python assertions must remain
enabled; do not use `python -O` or `PYTHONOPTIMIZE`.

## Continuum finite algebra

```bash
mkdir -p build
uv run --script certificates/continuum/continuum_maxwell_three_halves_certificate.py \
  --output build/continuum-certificate.json
```

This standard-library checker reconstructs the finite corner cluster and checks
its algebra, Hessian, placement, and rational inequalities. Its receipt states
the scope: “Finite corner-cluster algebra and placement only; not the continuum
proof.” The analytic proof is in the manuscript.

## Discrete Yee certificates

The original verifier sources and frozen inputs retain their internal paths and
bytes. A small partial replay needs NumPy and a C++17 compiler with its UBSan
runtime installed. On Linux distributions that split compiler runtimes into
separate packages, install the matching `libubsan` package as well:

```bash
uv run --with numpy==2.3.5 python certificates/yee/reproduce.py \
  --mode established-checks \
  --only logical composition h2-scalars original-defect-geometry pec kernel bulk-geometry \
  --workers 2 --run-dir build/yee-small
```

The output directory must be new. For the complete computational replay, first
install `yee-witnesses`, then run:

```bash
uv run --script scripts/assets.py install --groups yee-witnesses
uv run --with numpy==2.3.5 python certificates/yee/reproduce.py \
  --mode full --workers 2 --run-dir build/yee-full
```

The full run checks 604 H1 matrices, local witnesses, and 2,056 global-cover
matrices. It copies its inputs into an isolated run directory, checks frozen
hashes, executes the verifiers, and records individual receipts. Allow several
gigabytes of working space in addition to the downloaded data. Runtime depends
on the host and worker count.

For the detailed contract and failure semantics, see
[`yee/REPRODUCE.md`](yee/REPRODUCE.md). Installing `yee-receipts` also restores
the recorded reference run under `yee/recorded-run/`. These historical receipts
are useful for comparison and witness generation; they are not used as a
shortcut by a fresh computational replay.

## Provenance of the Yee documents

The documents under `yee/`, including `REPRODUCE.md` and the notes in
`yee/results/`, are preserved from the original research bundle and keep its
names. They therefore refer to files that this repository distributes under
other names or not at all:

| Original reference | In this repository |
| --- | --- |
| The eleven `maxwell_*` ZIP volumes rooted at `maxwell_sparse_reduction/` | `certificates/yee/` plus the `yee-witnesses` and `yee-receipts` archive groups |
| `work/bulk/` witness matrices | `yee/work/bulk/`, restored by `yee-witnesses` |
| `verification/publication_independent_retry/` | `yee/recorded-run/`, restored by `yee-receipts` |
| Other `verification/` runs and their monitoring and audit scripts | Not distributed; `reproduce.py` creates fresh runs |
| `theorem_and_proof.md`, `obligations.md` | Parts III and V of the Supplementary Information |

Run the commands above rather than the research-directory commands in
`REPRODUCE.md`; its description of the checks and their failure semantics
still applies.
