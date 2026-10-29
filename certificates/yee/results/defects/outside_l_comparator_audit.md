# Independent outside-L cover and scalar comparator audit

## Scope

`verify_outside_l_cover.py` independently checks the geometry of the
adaptive cover, the analytic Gamma region, and the scalar comparison that
transfers an original-crystal band bound to the inversion-symmetric
candidate. It distinguishes three gates:

1. A completed geometric cover with no pending or uncovered feasible leaf.
2. Matching current matrix-verification records for every proposed box.
3. Fresh exact interval matrix replay, performed once by the parallel
   canonical `work/bulk/global_certificate/verify_global.py` driver.

Matching saved records alone is not labeled a fresh matrix proof. The
default run exits nonzero until the geometric and fresh-replay gates have
passed. An explicit `--require-current-receipts` audit can exit successfully
after checking the complete geometry and all externally generated receipts;
it truthfully retains `matrix_replayed_this_run=false`. The top-level
reproducer combines that audit with its separately executed fresh matrix
replay. The full unique-edge theorem also needs the separately replayed H1
and local L-neighborhood certificates.

The completed proposal has **2,056 matrix boxes, 660 local-L boxes, one
Gamma box, and zero pending or uncovered feasible leaves**. The independent
tree traversal has 595 internal nodes and discards 1,449 infeasible leaves.
Those counts establish geometric completion; the fresh matrix run is a
separate premise.

Both computational gates have now been executed successfully. The fresh
canonical run in
`work/bulk/global_certificate/verification_final/reproduction_summary.json`
reports `ALL_2056_FULL_MATRIX_CERTIFICATES_REPRODUCED`, with zero
rejections, all source/proposal/witness integrity flags true, and runtime
971.56 seconds on six workers. The subsequent independent audit in
`results/defects/outside_l_cover_audit.json` accepted all 2,056 receipt and
witness bindings and all 84,296 scalar sign assumptions in 5.79 seconds.
Its status is `PASS_GEOMETRY_AND_CURRENT_RECEIPTS_EXTERNAL_REPLAY`: the
matrix computation is supplied by that immediately preceding canonical
run, not repeated by the auditor. This discharges the outside-L finite
comparison obligation. The final clean top-level reproduction remains a
separate aggregate check of all computational premises.

## 1. Independent geometry algorithm

The ordered FCC wedge is

\[
 W=\{0\le z\le y\le x\le1,\quad x+y+z\le3/2\}.
\]

Each dyadic box is reconstructed from its center, halfwidth, and depth.
The checker requires exact alignment with the octree of `[0,1]^3`,
rejects duplicate leaves and ancestor/descendant overlaps, and traverses
the resulting tree from its root.

The pilot uses a greedy minimal-point feasibility criterion. This checker
instead intersects nine rational halfspaces: six box faces, `y<=x`,
`z<=y`, and `x+y+z<=3/2`. It enumerates every nonsingular triple of
boundary planes, computes its exact vertex by the integer adjugate, and
checks all nine inequalities. The adjugate identity is itself checked
with integers. A bounded nonempty polytope has a vertex, including
lower-dimensional intersections, so this is an independent exact
feasibility decision. Dyadic scaling makes every comparison an integer
comparison.

A Gamma leaf is accepted only when its entire box lies in
`0<=x,y,z<=1/8`. A local-L leaf is accepted only when its entire box lies
in the Euclidean ball of radius `1/20` around `(1/2,1/2,1/2)`. For the
latter, the exact test is

\[
 \sum_j\max\{(\mathrm{lo}_j-1/2)^2,
                    (\mathrm{hi}_j-1/2)^2\}\le1/400.
\]

The maximum is attained at a box corner, so a center-only membership
test cannot be mistaken for full containment. Any feasible remaining
leaf without a matrix proposal is uncovered. Any nonempty pending input
list prevents completion, even if some pending boxes would later be
discarded as infeasible.

The original diamond material, including its exact scalar edge averaging,
has the 48 signed-coordinate-permutation symmetries already checked in
the H1 geometry certificate. Adding a constant scalar material preserves
all these symmetries. Thus the original-crystal comparator may be checked
on W. The perturbed material is **not** assumed to have cubic symmetry.
The comparison below transfers the bound separately at every Bloch point.

For completeness, duality with primitive translations
`(20,0,0),(10,10,0),(10,0,10)` gives the reciprocal vectors with all-even
or all-odd integer coordinates. The Voronoi zone is exactly

\[
 |\kappa_j|\le1,\qquad\sum_j|\kappa_j|\le3/2.
\]

Indeed, for an even reciprocal vector `2m`, its Voronoi inequality follows
from `4 sum |m_j| <= 4 sum m_j^2`. For an odd reciprocal vector, write
`|q_j|=1+2b_j`. Its inequality follows from
`2 kappa dot q <= 3+4 sum b_j <= sum(1+2b_j)^2`. Conversely, reciprocal
vectors `2e_j` and the eight sign vectors give all the displayed facets.
Taking absolute values and sorting coordinates therefore maps every point
of the full zone to the checked wedge.

The eight signed L centers form four reciprocal-lattice classes: opposite
centers differ by an odd reciprocal vector, while centers with a mixed
sign change do not. Signed coordinate permutations preserve Euclidean
distance, so the excluded wedge ball and its symmetry images are exactly
the local neighborhoods handled by the four independent local
certificates, with the usual reciprocal identification at the zone faces.
The checker explicitly matches the four representative centers to the
primitive doubled characters `(1,1,1),(1,1,0),(1,0,1),(1,0,0)` used in the
local witness files. It also checks the primitive cell volume 2,000 and
the conventional-to-primitive folding index four.

## 2. Analytic Gamma exclusion

Use

\[
 t=1/64,\quad s=157/16384,\quad\sigma=2^{-24}.
\]

The original shifted electric operator is

\[
 H_0-sI=C^*C-tD',\qquad D'=D_0+64sI,
 \quad I\le D'<13I.
\]

On `|q_j|<=1/8`, the free low electric eigenvalues are at most

\[
 a_0=12\sin^2(\pi/160).
\]

All other free eigenvalues are bounded below by the minimum of

\[
 a_1=12\sin^2(7\pi/160),\qquad
 a_2=4\sin^2(15\pi/160).
\]

These follow from the odd/even FCC reciprocal representatives. There
are exactly `N+2` low electric curl-curl eigenvalues, including the
longitudinal modes and the two low transverse modes; at Gamma their
merged zero eigenspace still has that same dimension. The remaining
free eigenvalues satisfy the displayed lower bounds.
Away from Gamma, each Fourier curl symbol has a one-dimensional kernel
and two transverse eigenvalues, so the low count is `N+2`. At Gamma the
zero Fourier symbol contributes three kernel directions and the other
`N-1` symbols contribute one each, again giving `N+2`.

The independent checker uses rational alternating-series bounds for
Machin's formula for pi, `sin(x)<=x`, and
`sin(x)>=x-x^3/6` on the small positive interval involved. It proves

\[
 a_0<t-\sigma,\qquad
 a_1>13(t+\sigma),\qquad
 a_2>13(t+\sigma).
\]

Eigenvalue comparison therefore gives exactly `N+2` negative electric
eigenvalues and no zero eigenvalue for every squared frequency in
`[t-sigma,t+sigma]`. Congruence by `D'^(1/2)`, with `D'>=I`, yields an
electric gap at least `sigma` for `H_0-sI`. This handles the singular
projector point at Gamma analytically.

## 3. Matrix boxes and perturbation transfer

Each nonanalytic box must independently certify the same negative count
and the same frequency interval for the same uniformly shifted original
material. The current exact interval checker uses a 48-bit fixed-point
kernel, compiled with undefined-behavior sanitization, and verifies every
proposed norm and inertia inequality from its finite witness arrays.

The geometric auditor checks that each saved record matches its exact
box, shift, frequency interval, negative count, proposed constants, source
hashes, and witness hash. A fresh replay does not use the saved `PASS`
string as its decision: it rebuilds the kernel and calls the exact
`verify_record` operation on every box.
The only permitted modification of proposed constants is a power-of-two
increase of the first two central residual bounds, capped at `1/128`; the
exact verifier recomputes all scalar margins with those larger bounds.
All other constants must remain unchanged.
The checker also verifies the sign premise of every proposed norm and
radius bound before reading receipts: all 84,296 scalar values in the
13 bound fields are nonnegative, and the field norms and two denominator
radii are strictly positive. This is necessary because a norm routine
that squares its proposed bound must not interpret a negative number as
a valid norm upper bound. The check uses exact fractions for every input.

The independent link audit additionally requires a nonempty, distinct,
integer Fourier low set in `0,...,1999`, and exact agreement of the NPZ
center and halfwidth with the dyadic proposal. Every canonical receipt
binds the full proposal bytes, its individual JSON record, all six current
verifier source files, and the witness bytes before and after replay.
Receipt and witness hashes are checked again during the independent
audit, with proposal and source hashes checked before and after the whole
audit. Output is written atomically and read back; an interrupted audit
cannot leave a new completed acceptance record.

If the complete cover passes, then for every original Bloch fiber outside
the L balls the first positive electric eigenvalue is at least `s+sigma`.
The negative-count statement is essential: an invertibility assertion
alone would not identify which side of the shifted gap contains the
physical positive bands.

The canonical inversion-symmetric scalar perturbation satisfies

\[
 H_0-\rho I\le H_{\rm p}\le H_0,
 \qquad \rho=1023/2^{26}<1/4096.
\]

H1 and this strict perturbation bound preserve the number of negative
electric modes. Applying finite-dimensional min-max to the first
positive rank gives

\[
 \lambda_{\rm p,+}(q)\ge s+\sigma-\rho
       =\frac{642053}{2^{26}}
\]

outside all local L balls. The exact scalar checker verifies that this
threshold exceeds the upper residual interval for the lowest L value by
more than `1/500000`. Combined with the whole-ball local certificates and
the strict ordering of the four L values, this certifies a unique simple
global Morse edge at L++-. The complete assembly and its separate local
and H1 dependencies are stated in
`../main/global_edge_assembly_audit.md`; this outside-region audit does
not substitute for those other checks.

## 4. Replay

From the research root, the canonical parallel fresh replay is:

```bash
python work/bulk/global_certificate/verify_global.py --workers 6 --output artifacts/global_atomic
```

It requires an empty output directory and writes one closed, atomic
receipt per freshly checked box. The independent audit then reads only
the receipts produced by that run:

```bash
python results/defects/verify_outside_l_cover.py --proposal work/bulk/global_certificate/cover_proposals.json --matrix-dir work/bulk/global_certificate --receipts-dir artifacts/global_atomic/accepted_points --require-current-receipts --output artifacts/outside_l.json
```

This audit exits zero only for complete geometry and complete current
canonical receipts. Its status is
`PASS_GEOMETRY_AND_CURRENT_RECEIPTS_EXTERNAL_REPLAY`, and its
`matrix_replayed_this_run` field remains false. The successful immediately
preceding driver execution supplies the fresh-replay premise.

A geometry-only run without `--require-current-receipts` exits with status
3 when geometry is complete, to distinguish that result from a full fresh
proof. An incomplete cover exits with status 2. As a convenience, a single
command can delegate the parallel fresh replay to the canonical driver
and then audit its new output:

```bash
python results/defects/verify_outside_l_cover.py --replay-matrices --workers 6 --output artifacts/outside_l_standalone.json
```

The final command requires a new `artifacts/outside_l_standalone_fresh_matrices`
directory and recomputes every matrix acceptance. It does not replace the
independent H1 and local L-point/ball replays. The checkpoint JSON records
geometric completion, receipt completion, and fresh matrix replay as
distinct fields.
