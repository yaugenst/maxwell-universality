# Reproduce the computational premises

**The discrete reduction is proved by ordinary analytic arguments plus
the exact finite certificates described here.** The final clean 22-job
replay and postflight integrity audit passed; `obligations.md` records
their precise scope. Successful numerical exploration or stored acceptance
JSON does not replace fresh exact/interval verification. The top-level
runner executes those verifiers and keeps the analytic proofs separate.
The fixed defect/coupling selection is proved terminating, not reported
as executed, and the randomized-SLTH consequence is separately conditional.

## Full replay

The complete distribution consists of the main
`maxwell_sparse_reduction_proof.zip`, two `maxwell_h1_evidence_partN.zip`
volumes (N=1,2), and eight `maxwell_global_evidence_partN.zip` volumes
(N=1,...,8). Extract all eleven archives into the same parent directory;
they share the root `maxwell_sparse_reduction/`. Repeated canonical source
entries in the evidence volumes are identical. The main archive contains
the proof, local witnesses, acceptance sources, manifests, and retained
run evidence; the ten separate volumes supply the large H1/global matrix
witnesses. Main-archive-only extraction is insufficient for a full replay.

Archived run snapshots retain their verifier sources and generated
acceptance artifacts. Canonical inputs are supplied once at their root
paths, and each run's input manifest identifies the exact bytes needed to
reconstruct its input snapshot. A new full replay creates a complete new
snapshot automatically. The historical `checkpoint` entry in
`verification/saved_artifacts.json` identifies the earlier saved checkpoint;
it is not the digest or version of the final archive containing that file.
The final archive identity and hash are provided separately with delivery,
avoiding a self-referential archive digest. The ten witness volumes are
unchanged from their recorded identities.

From the research directory containing this file:

```sh
python reproduce.py
```

The default is `--mode full`. It includes the complete global outside-L
coverage gate and executes 22 fresh checks. Missing canonical evidence,
incomplete coverage, a failed matrix inequality, disabled assertions, a
subprocess failure, or a changed staged input produces a nonzero exit.
Such a failure must not be reclassified as proof by excluding its
dependency.

The default creates a new directory under `verification/runs/`. A chosen
new location and atomic-replay concurrency can be supplied explicitly:

```sh
python reproduce.py --workers 4 --run-dir verification/my_fresh_run
```

The final accepted run is retained at
`verification/final_clean_all_dependencies_retry/`. Use a different new
run directory for reproduction. A monitoring wrapper, which prints a
heartbeat and forwards the unchanged controller's exit status, is also
available:

```sh
python -u verification/monitor_reproduction.py --workers 6 --run-dir verification/my_monitored_fresh_run
```

The wrapper does not change acceptance tests, skip matrix checks, or turn
partial records into acceptance.

The run directory must not already exist. The runner copies the required
source and canonical input bytes into `my_fresh_run/snapshot/` before
executing them. It does not overwrite earlier accepted logs or the frozen
H1 source/witness archive. Copies, rather than hard links, isolate the new
run from source files which generate outputs beside their own code.

All paths recorded in the input manifest and check commands are relative
to the snapshot. Moving the research directory does not require editing
workspace paths. The recorded Python executable and runtime details are
provenance, not hard-coded restart requirements.

## Environment

The recorded final-run environment is Python 3.12.14, NumPy 2.3.5,
g++ 13.3.0, and x86_64 Linux. A compiler supporting C++17 and signed
`__int128` is required for the interval kernel. Kernels are compiled with
undefined-behavior sanitization and halt on the first sanitizer error.
Do not use Python `-O`, set a
nonzero `PYTHONOPTIMIZE`, disable C++ assertions, or bypass arithmetic
capacity guards. The top-level script rejects optimized Python before
running checks; its child processes also keep assertions enabled.

SciPy is used by some exploratory witness generators, but is not needed
by the listed fresh acceptance tests. The runner records its version if
installed without making it an acceptance dependency. It records Python,
platform, NumPy, compiler version, and actual compile commands in the run
metadata and child logs. BLAS/OpenMP thread counts are fixed to one per
worker. The default worker count is four; `--workers` changes that
count, not the number of BLAS threads.

For a clean machine with Python 3.12 and a suitable compiler already
installed, an optional isolated Python setup is:

```sh
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install numpy==2.3.5
python reproduce.py --workers 6
```

These setup commands document dependencies; they were not an additional
test run. Installing NumPy may require network access. The verification
run itself uses the included local source and canonical witness files.

No network access, paid computation, account, or externally hosted solver
is part of reproduction. Missing Python/compiler dependencies must be
installed in the chosen environment before the decisive run; they are
not silently substituted by stored results.

## What each fresh check establishes

| Group | Fresh operation | Scope |
|---|---|---|
| `logical` | `results/logical/verify_logical.py` | Exact circuit, routing, path inverse, and residual identities on the specified finite cases. The all-input R5 proof remains analytic. |
| `composition` | `results/main/verify_composition.py` | Exact mediator, Schur, and related algebraic identities used by the physical composition. |
| `h2-scalars` | Author and independent exact scalar checkers | Rational constants in the generic H2 existence argument. They do not execute its enormous fixed search or certify H3. |
| `original-defect-geometry` | Independent integer geometry checker | The original diamond and 392-air-cell defect incidence counts; no spectral assertion. |
| `pec` | Independent finite PEC incidence checker | Boundary indexing, four incident cells/faces, and uniform scalar shift behavior on the checked boxes. The arbitrary-size argument is analytic. |
| `kernel` | Exact endpoint/UBSan adversarial checks | Supplementary checks of the interval arithmetic primitives. They do not replace the audited arithmetic proof. |
| `bulk-geometry` | Independent H1 geometry and coverage checker | Full FCC-domain geometry and the 604 required original-gap boxes. Matrix acceptance is separate. |
| `h1` | Atomic fresh replay of every H1 matrix | All 604 exact interval matrix checks, atomic point receipts, aggregate consistency, independent geometry, and finalization. |
| `local-inertia` | Fresh two point brackets and uniform-neighborhood matrix | Original point shifts 1/256 and 5/256, then the 7/256 neighborhood count with spectral halfwidth 1/4096. No eigensolver regeneration occurs. |
| `local-defect` | Exact point residuals and four curvature/Gram checks | The frozen inversion-FCC material, all four L-point inclusions/parities/order, and the finite Hessian/Gram inequalities used by the neighborhood proof. |
| `local-scalar` | Exact polynomial-neighborhood closure | Rational Taylor/remainder and spectral-polynomial constants for radius 1/20. The finite matrix inputs are the preceding checks. |
| `global` | Complete outside-L matrix and independent coverage replay | Every required shifted-background matrix plus exact full-domain coverage, Gamma inequalities, and compatibility with the certified local neighborhoods. This gate is mandatory in full mode. |

The H1, local-inertia, and global groups each begin with a fresh exact
sign-premise check using `results/bulk/audit_fixed_parameters.py`.
It proves all supplied norm bounds are nonnegative and the required
norm/radius/residual bounds are strictly positive. This is necessary
because some interval norm routines compare squared bounds. The matrix
subprocess is blocked if its sign check fails. For the current frozen
inputs, these three checks cover 109,265 scalar parameters in 2,665
records; they do not replace any matrix computation.

Checks run in separate Python subprocesses. In particular, the original
H1 and shifted-background directories contain modules with the same names
but different material/kernel constants. They must not share an imported
`verify_point` or `interval_tools` module in one Python process.

## Frozen H1 evidence and the rejected older assembly

The original 613-entry source/witness manifest remains unchanged:

```text
work/bulk/clean_certificate/evidence_manifest.json
SHA-256 f8c0625768ec5c7705408325d49e010195790379b65096b8fb65231543542de0
```

The accepted canonical wrapper is
`work/bulk/clean_certificate/verify_atomic.py`, bound by
`atomic_driver_manifest.json`. Its direct command is:

```sh
python -u work/bulk/clean_certificate/verify_atomic.py --workers 6 --output NEW_DIRECTORY
```

For a fresh end-to-end reproduction, use the top-level runner so output
side effects are isolated in the snapshot. The direct frozen finalizer
also writes a strengthened-box record beside its own source.

An earlier replay's finalizer correctly rejected shard 2 because its
metadata declared 55 checks while the bound JSONL file retained only 11.
Matching file hashes and metadata counts were insufficient. The atomic
wrapper instead closes, flushes, hashes, and reads back each individual
point record, then constructs and reads back the aggregates. A later
complete atomic replay passed all 604 checks and finalization; its accepted
record is `verification_atomic_final/reproduction_summary.json` beneath
the H1 directory. That historical successful record is retained for
inspection; the top-level runner executes the matrix tests again.

## Local and global input identities

The local exact scalar material is
`results/defects/inversion_edge_material.json`. Its five NPZ witness files
are:

- `make_inversion_point_witnesses.npz`;
- `explore_inversion_edge_feshbach.npz` for L++-;
- `inversion_feshbach_lppp.npz`;
- `inversion_feshbach_lpmp.npz`;
- `inversion_feshbach_lmpp.npz`.

They are untrusted dyadic proposals. The exact checker reconstructs
incidence operators, parity, residuals, error bounds, and rational matrix
inequalities. The `--output` options put new point and curvature
acceptances in the snapshot's `artifacts/` directory. No earlier point or
curvature acceptance is copied into these output locations.

The global gate uses
`work/bulk/global_certificate/cover_proposals.json`, the adjacent
`frozen_manifest.json`, its exact verifier sources, and all named witness
files. The frozen source manifest binds the proposal, each matrix witness,
and the six acceptance/geometry source files. Its SHA-256 is
`bee245fc7edab8fd2de51a4876de665879fc7a9542dfb2a4725fa47a895d100c`;
the top-level controller rejects a different manifest. The fresh command is
`verify_global.py --workers N --output NEW_DIRECTORY` in that directory.
It verifies every matrix, uses atomic point receipts and aggregate
readback, and checks the exact geometric cover. The top-level controller
runs it on the isolated snapshot with outputs under
`artifacts/global_atomic/`.

It then executes `results/defects/verify_outside_l_cover.py` with
`--require-current-receipts` against those newly generated
`artifacts/global_atomic/accepted_points/` receipts. The independent audit
must report complete geometry and complete input/receipt bindings. Its
`matrix_replayed_this_run` remains false: the immediately preceding
atomic subprocess is the fresh matrix computation. Both subprocesses
must succeed in the same top-level run. No old accepted receipt is
copied into the fresh global output directory.

These paths can be supplied as project-relative `--global-proposal` and
`--global-matrix-dir` arguments if the retained directory layout changes;
the proposal must remain `MATRIX_DIR/cover_proposals.json`, as required
by the frozen driver.
The independent outside-L checker performs exact polytope/tree coverage
and Gamma comparisons. A receipt-consistency audit alone is not a fresh
matrix replay. Full mode must execute every required matrix in the current
run, then check that the complete geometric cover refers to those same
inputs. The root proof and ledger specify the current global acceptance
state; this document does not infer completion from a proposal count.

## Run artifacts and exit status

Each run contains:

- `runtime.json`: interpreter, package, platform, and compiler provenance;
- `input_manifest.json`: relative paths, byte counts, roles, and SHA-256
  digests of every copied source and canonical input;
- `logs/`: complete combined stdout/stderr for every launched check, or
  a preflight failure trace if a required input was unavailable;
- `jobs/`: structured command, timing, exit code, output hashes, and
  failure information per check;
- `snapshot/`: the exact isolated inputs and freshly generated outputs;
- `run_summary.json`: the selected scope, all step results, final input
  integrity check, and completion disposition.

A full successful run exits zero and records
`ALL_COMPUTATIONAL_PREMISES_REPLAYED_ANALYTIC_PROOF_SEPARATE`. This means
that the listed computational premises were freshly checked. It does not
assert that ordinary analytic arguments have been formalized in a proof
assistant or independently turn the mathematical report into a theorem.
Failed or incomplete full runs exit 2 and record
`FAILED_OR_INCOMPLETE_OPEN`; an interrupted run exits 130 when the
interruption can be recorded. A hard process/container kill can leave a
`RUNNING` summary, which is not a pass.

After a new successful full replay, an optional separate postflight audit
can rehash its inputs and bind its retained job, receipt, and coverage
evidence:

```sh
python verification/audit_final_evidence.py --run verification/my_fresh_run --output verification/my_fresh_evidence_audit.json
```

This audit must target the complete new snapshot, not an archived snapshot
from which duplicate canonical inputs were omitted for distribution. It
does not perform a new matrix replay or validate the analytic proofs.
The delivered final run's already-executed postflight audit is retained at
`verification/final_evidence_audit.json`, with status
`PASS_FINAL_EVIDENCE_INTEGRITY_AND_BINDING`.

`--step-timeout SECONDS` is optional. A timeout fails the affected check;
it is never interpreted as acceptance. The default does not impose an
unverified runtime cutoff on the global certificate.

## Explicit partial mode

To explicitly rerun the established groups without claiming a full replay:

```sh
python reproduce.py --mode established-checks
```

To run a named subset for debugging the controller:

```sh
python reproduce.py --mode established-checks --only logical composition h2-scalars local-defect local-scalar
```

Both forms are explicitly **NOT FULL VERIFICATION**, even when every
selected check succeeds. The summary records unselected groups and
`full_reproduction_complete: false`. `--only` is rejected in full mode.
`--list-checks` prints the selected inventory without running or claiming
verification.

## Observed resources and tests

The frozen H1 manifest contains 660,736,466 bytes of input files. A fresh
snapshot copies these bytes once if H1 is selected, plus the selected
local/global sources and witnesses. The current frozen global archive
contains 2056 witnesses totaling 2,385,405,573 bytes, as measured by its
preflight. These counts describe this exact archive, not a guessed bound
for a later replacement cover. Including the local inputs, allow about
3.1 GB for unpacked canonical arrays and another 3.1 GB for a fresh full
snapshot. Retaining all distributed ZIP parts as well gives an estimated
9.2 GB before additional runs and temporary outputs; 12 GB of free disk is
a reasonable planning allowance, not an enforced or portable resource
bound. Each extra full run retains its own snapshot and logs until
deliberately archived or removed.

The canonical atomic H1 replay on this environment took about 280.3 seconds
with six worker processes. The canonical 2056-matrix global replay took
971.565 seconds with six workers; observed peak memory was about 115 MB
per worker. The final combined clean run completed all 22 jobs in
1485.886 seconds (about 24 minutes 46 seconds). Its controller recorded
300.487 seconds for the H1 subprocess, 1109.524 seconds for the global
subprocess, and 7.215 seconds for independent global receipt/geometry
binding. These are observed wall times, not portable resource bounds.
The local exact point/curvature checks have taken roughly 1–3 seconds
each in this environment. Use the recorded platform and actual witness
sizes when choosing worker counts elsewhere.

The controller's initial clean partial smoke run freshly passed the
logical, composition, both H2 scalar, original defect geometry, PEC,
four-point residual, all four curvature/Gram, and local scalar checks.
Its `NOT_FULL` status is retained in
`verification/controller_smoke_20261027/run_summary.json`. A separate
interval smoke passed the independent H1 geometry, both point inertia
brackets, and uniform local isolation. That smoke found a relative C++
include-path error in the controller's endpoint-test invocation; the
controller now resolves child path arguments against the isolated
snapshot, and the endpoint test then passed in
`verification/controller_kernel_repaired_20261027/`. Missing-input and
optimized-Python trials both failed closed.
The final all-dependency replay after the last substantive verifier change
passed all 22 checks in `verification/final_clean_all_dependencies_retry/`,
with no unselected groups and all staged inputs unchanged. Its terminal
summary has SHA-256
`d3c4cc4877468fe2dbb0e8703317a75706df4eaf865246b3db78e88405a9f102`.
The earlier `verification/final_clean_all_dependencies/` attempt has no
terminal acceptance and remains explicitly incomplete; none of its partial
global receipts were reused by the successful retry.
