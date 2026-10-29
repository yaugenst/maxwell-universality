# Audit of the shifted outside-L comparator

## Scope and evidence

The target here is the complete outside-L comparison for the original cubic diamond material after the uniform electric shift `s=157/16384`. It is a finite prerequisite for the separately audited unique Morse band edge argument. It is not a claim about the full sparse Maxwell reduction by itself.

The canonical fixed evidence is `work/bulk/global_certificate/`. Its frozen manifest has SHA-256 `bee245fc7edab8fd2de51a4876de665879fc7a9542dfb2a4725fa47a895d100c`. The complete proposal has SHA-256 `b90a4820ebf763da72ff23e46fcbe542fae9dc50ac82a8492f2eb0641afd8343`. There are exactly 2,056 witnesses, totaling 2,385,405,573 bytes. This file records the mathematical and implementation audit; completion of the full computational acceptance must be established separately by the canonical fresh replay's terminal summary and actual atomic point receipts.

**The canonical fresh replay has completed with exit code zero.** `work/bulk/global_certificate/verification_final/reproduction_summary.json` reports `ALL_2056_FULL_MATRIX_CERTIFICATES_REPRODUCED` and `CERTIFIED_WITH_EXACT_COVER`. All 2,056 full matrix checks ran under UBSan, all atomic receipt readbacks and current witness/source/proposal hashes passed, and the exact complete geometry was rechecked at finalization. Runtime was 971.564551 seconds with six workers. A copy is `results/bulk/global_reproduction_summary.json`.

The terminal summary hash is `fc4f3845642e75345b51aed55cd4e129e50a0a4f193def7984451608fd29e4ce`. The complete freshly rebuilt `all_verified_boxes.jsonl` has hash `a8d77641f30e3abbd118fc8c3842adeda37326fcdabb409f28632d7ae3289d71`. The frozen manifest remained unchanged. The terminal log marker is `GLOBAL_ALL_2056_FRESH_MATRIX_CHECKS_AND_EXACT_COVER_PASS`.

Across all boxes, the four exact scalar Schur-test margins have the following conservative rational lower bounds: negative-block margin greater than `2/5`, positive diagonal margin greater than `3/40`, gradient margin greater than `73/100`, and positive determinant margin greater than `3/500`. These are the normalized scalar acceptance margins, not the physical band-energy gap. The summary retains their complete exact rational minima.

The scope remains the outside-L comparator. Its deliberately false `global_spectral_edge_certified` field means that the separate local spectral/curvature certificates and analytic composition must still be supplied; it does not indicate a failure of this outside-L replay.

The separate final cover audit completed with exit code zero in 5.79 seconds. `results/defects/outside_l_cover_audit.json` binds all 2,056 current receipts to the exact proposal, six sources, witnesses, record metadata, and interval inequalities; it independently checks all 84,296 scalar sign premises and the full rational-polytope cover with no pending or uncovered region. Its SHA-256 is `ef080e0812e4099d307f0f0d64556ba8485018057532d2f2d8b86e9864a8a0a8`. This audit does not substitute for the fresh matrix replay; it checks the completed replay's geometry and evidence links independently.

The acceptance sources have these hashes:

| File | SHA-256 |
|---|---|
| `verify_global.py` | `e5d7dddbc6a90deb860b4b0339540073e1a8f5808b85ff5d276b0166df1a3263` |
| `verify_cover.py` | `9f287f2c45c30924826998732ef05d3eb6449855f3f069d76fe66957f6a7e51a` |
| `verify_point.py` | `f089de98a622aefdc9ecd7a458b26e5c4431575406efa63f2613245e0dccdbab` |
| `interval_tools.py` | `8be382bb263f5454be68cc8d023c6c4fc0d0a0714652afd8249cb8f83a77fed1` |
| `interval_kernel.cpp` | `ed01633640acdb5f458f8b976ff1731f3157715c852dcb0de2f9fe9cb4c587df` |
| `exact_geometry.py` | `7f5ba3dc39978079c5b486d7453a6ac230095e9f0c9e6609ae7bfd5fb4e2df57` |

## Exact operator transformation

For the original scalar edge average `D0`, let

\[
H_0=C^*C-D_0/64,
\quad s=157/16384,
\quad D_s=D_0+(157/256)I.
\]

Then `H0-sI = C*C-Ds/64` exactly. If `den` is the original sum of the four incident cell permittivities, the new edge average is

\[
D_s=(64\,\mathrm{den}+157)/256.
\]

The Python verifier constructs the integer denominator `64*den+157`, and the C++ material multiply uses numerator 256. Thus every material inverse is the exact rational `256/(64*den+157)`. The five possible original sums remain `{4,15,26,37,48}`; the new integer denominators are `{413,1117,1821,2525,3229}`. The maximum material is `3229/256 = 12.61328125 < 13`, and the minimum is greater than 1.

The high Fourier transverse block uses `lap/13-t` both in its central inverse weight and its displaced-box scalar estimate. The frequency interval is `t±sigma`, with `t=1/64` and `sigma=2^-24`. The fixed number of negative transverse modes is two. No part of this argument changes the geometry, Fourier lattice, or curl symbol of the original material.

The magnetic/electric correspondence and the Schur complement argument are the same identities audited in `audit.md`. If all box checks and Gamma comparisons pass, the normalized magnetic positive spectrum avoids `[t-sigma,t+sigma]` and has precisely two eigenvalues below the interval. Electric congruence yields a spectral gap of at least `sigma` for `H0-sI`, because `Ds>=I`. The original H1 gap at zero fixes the electric negative count at `N+2`; since the shifted matrix has the same negative count, every positive original electric eigenvalue outside the L balls is at least `s+sigma`.

The separately specified scalar perturbation satisfies `0<=delta_cell<=1023/2^20`, and averaging preserves that bound. Its electric perturbation is negative semidefinite with norm at most `rho=1023/2^26`. Since `rho<1/4096`, the original negative bands remain negative. Min-max comparison gives the perturbed positive-band lower bound

\[
s+\sigma-\rho=642053/2^{26}.
\]

The exact arithmetic comparator checks that this exceeds `23913/2500000` by more than `1/500000`. A separate point certificate must establish that the selected local lowest eigenvalue is below `23913/2500000`. The global comparator does not read or trust a local stored PASS string to establish this dependency.

## Exact geometry and analytic Gamma region

The original material is invariant under the full 48-element signed permutation group. Its reciprocal lattice is the all-even/all-odd integer lattice; its closed Voronoi zone reduces to

\[
W=\{0\le z\le y\le x\le1,\ x+y+z\le3/2\}.
\]

Uniform scalar shifting preserves all these symmetries. The eight signed half-integer L centers fall into four equivalence classes modulo the reciprocal lattice, with each class containing a center and its negative. The local perturbation need not preserve the 48 symmetries: the global exclusion is first proved for the symmetric unperturbed comparator and then transferred through the uniform operator norm bound. The local perturbed analyses are performed at all four inequivalent centers separately.

The independent feasibility method enumerates all nonsingular triples of nine halfspace boundary planes. Because the intersection of the box and wedge is a bounded polytope, it is nonempty exactly when at least one such vertex satisfies all nine halfspaces. All determinant, inverse-adjugate, and inequality calculations use integers or exact fractions. This method differs from the pilot generator's greedy feasibility test.

A dyadic tree starting with `[0,1]^3` is reconstructed from the proposed leaves. Duplicate leaves, repeated witness names, overlapping ancestor/descendant leaves, missing feasible leaves, pending leaves, and unused listed leaves are all rejected. No finite-resolution sampling is used for spherical exclusion: a box is inside the radius-1/20 L ball exactly when the sum of its three farthest coordinate-square distances is at most `1/400`.

The final tree has 595 internal nodes and 4,166 terminal leaves: 2,056 matrix leaves, 660 L-ball leaves, one Gamma leaf, and 1,449 infeasible leaves. Matrix-box depths are 4 through 9, with counts `{4:502, 5:501, 6:409, 7:313, 8:33, 9:298}`. The deepest halfwidth is `1/1024`.

The sole analytic Gamma box has all coordinates between 0 and `1/8`. Exact Machin-series bounds for pi and the elementary inequalities `sin(x)<=x` and `sin(x)>=x-x^3/6` prove

\[
12\sin^2(\pi/160)<t-\sigma,
\]

\[
12\sin^2(7\pi/160)>13(t+\sigma),
\quad
4\sin^2(15\pi/160)>13(t+\sigma).
\]

These separate the q=0 low sector from all other Fourier sectors even at Gamma, where the transverse projection formula is singular. The proof uses min-max comparison with `I<=Ds<=13I`, so no singular projector is evaluated in the Gamma region.

The original pilot unnecessarily forced subdivision whenever a box center lay inside the full radius-1/20 ball. For a curved boundary, this rule could perpetually split boundary-straddling boxes without trying an otherwise valid matrix certificate. It was changed before the final cover was constructed: only centers inside radius `1/25` skip the spectral test; full-box exclusion still uses radius `1/20`. Therefore the matrix-valid annulus overlaps the local region. This change affects proposal generation, not the acceptance criterion: every proposed matrix box is fully verified, and every excluded box is checked for full containment.

## Complete integer-range argument for the 48-bit kernel

The kernel represents a complex rectangular interval by signed 64-bit centers and a nonnegative signed 64-bit radius, divided by `S=2^48`. Python scalar interval arithmetic uses 100 fractional bits with unbounded integers. All witness shapes, metadata, finite values, index bounds, and input magnitudes are checked before C++ receives their arrays. Witness values have magnitude below 1,000; multiplying by `S` is therefore safely below `2^58`. Any final quantization defines an exact dyadic witness and is not treated as a verified approximation to an eigenvector.

The norm and radius parameters are also mathematically nonnegative. This is checked explicitly for the fixed proposal by `check_global_parameters.py`: all 84,296 such scalars across the 2,056 boxes are nonnegative, and all field norms and low/high Fourier radii are strictly positive. This sign premise matters because the generic matrix norm helper squares a proposed norm bound. Its squared check alone would not distinguish a negative proposed bound; no negative bound occurs in the frozen certificate. The exact sign audit and proposal hash are recorded in `global_parameter_sign_audit.json`.

The integer-range arguments in `audit.md` remain valid with 48 replacing 52; the smaller scale increases the permitted physical range. The full inventory is as follows.

1. Addition, subtraction, negation, and conjugation promote signed-64 operands to signed 128-bit before arithmetic. Their intermediates need at most 65 bits. Every conversion back to 64 bits is checked. Absolute value rejects `INT64_MIN` before negation.

2. Complex multiplication checks `|center|+radius<2^62` separately for both real and imaginary components of each factor. For `R=2^62`, the real and imaginary center numerators have magnitude below `2R^2<2^125`. The radius numerator is bounded by `2R(r+s)-2rs<=2R^2`. Also `|a_x|+|a_y|<2^63`, so the source's one 64-bit sum in that radius expression is safe. Centers are divided by `S`, and the radius uses an outward ceiling plus one to cover center rounding. All output conversions are checked.

3. Rational scaling uses products of signed-64 quantities promoted to signed 128-bit, of magnitude below `2^126`. Denominators must be positive. The minimum signed multiplier is rejected by the absolute-value guard, and output conversion and outward-radius increment are checked.

4. Positive-real division has endpoint numerators `m±r` of magnitude below `2^64`. Multiplication by `2^48` therefore has magnitude below `2^112`, well inside signed 128-bit. Positive denominator endpoints lie between 1 and `2^64-2`. Signed floor/ceiling quotients and their radius-enlarging differences fit signed 128-bit. Final conversion is checked. The exact denominator targets are real by construction; their rectangular imaginary error is not used to change that exact identity.

5. A square-root argument satisfies `0<=r<=x<=INT64_MAX`. Its scaled upper endpoint is below `2^112`, so the integer square root is below `2^56`. The unsigned-to-signed casts, outward upper increment, midpoint, and endpoint differences are therefore safe in signed 64-bit. The bit-pair integer square-root algorithm uses only unsigned 128-bit arithmetic within these bounds. Its hardened postconditions check `root^2<=input<(root+1)^2` directly. Thus no correctness claim depends only on a floating square-root estimate.

6. Each complex Gram-product summand is below `2^125`. The complete 6,000-row sum is not assumed to satisfy an unchecked a priori bound: each signed-128 addition is guarded by `__builtin_add_overflow`; an overflow aborts acceptance. The allowed denominator power is 0 through 70, so `S<<power` is at most `2^118`, which fits signed 128-bit. Every quotient-to-64 conversion is checked.

7. The actual frozen witnesses have low dimensions from 10 through 15, so every transverse block has at most 30 columns. All Gram/PSD matrix orders are at most 30. Their dimension products and indices fit signed 32-bit. Fourier arrays have 2,000 points and three components, so flattened point/column indices are below 180,000. The FFT stack arrays have length 20, and recursion uses only the supported lengths 20, 10, 5, 2, and 1. Root indices lie in 0 through 19, and phase products have magnitude at most 342. All new material denominators are positive and below 3,230.

8. PSD rescaling inspects valid signed-64 centers and nonnegative radii. Its exponent is at most 48 and at least -15, so every rational scaling factor fits signed 64-bit. It rejects negative radii and `INT64_MIN` centers before NumPy absolute values are taken. The only in-place NumPy center addition restores a root of unity by adding `S` to a curl-symbol component; the exact component has magnitude at most 2, far below the signed-64 limit. Other conversions from the arbitrary-size Python scalar layer use NumPy's checked signed-integer construction on fixed, bounded parameters.

The interval LDL checker accepts only when every real pivot interval has strictly positive lower endpoint. Any checked overflow or failed pivot rejects or aborts the current acceptance. Assertions remain enabled: the compile command contains `-O2` but does not define `NDEBUG`; the Python driver rejects optimized assertion-disabled execution. UBSan is additionally enabled for every operation of every full fresh matrix check. These runtime checks supplement the mathematical range argument and do not replace it.

The original 52-bit checker aborted on a diagnostic interior point because a weighted positive vector exceeded its conservative physical multiplication guard. The observed event was an explicit assertion failure, not an observed signed-overflow event. The complete log and constants were retained in `edge_assessment/inside_diagnostic_full.log` and `inside_diagnostic_constants.json`. A separate 48-bit checker verified that same diagnostic point under UBSan. The final outside-L acceptance uses 48 bits throughout; the integer guard and checked overflow machinery remain in place.

## Integrity and falsification discipline

The full preflight rejected three truncated historical pilot NPZs before the final manifest was frozen. Their sizes were approximately 91 KB; regenerated complete files are approximately 1.1–1.3 MB. The rejected hashes and provenance are preserved under `global_certificate/rejected_input_evidence/`, and the repairs under `input_repairs/`. All three regenerated constant dictionaries were exactly identical to their original proposals. The cover proposal was therefore preserved byte for byte.

The final driver binds every receipt to the byte hash of the complete proposal, the canonical JSON hash of its individual record, all six source hashes, the frozen manifest hash, and the witness hash before and after the matrix check. Receipt writes use a temporary file, flush/fsync, atomic rename, immediate byte readback, and a repeated SHA-256 check. Finalization rereads every expected receipt, rejects missing or extra accepted files or any rejected file, rehashes all witnesses and sources, reruns exact geometry, and only then writes the aggregate and terminal summary.

Historical stored PASS records, floating eigensolver output, scalar pilot screens, and partial streaming batches are never accepted as substitutes for this fresh full computation. The trusted computational base remains Python integer/Fraction arithmetic, NumPy representation and array plumbing, the inspected interval kernel, the compiler/runtime, and hardware arithmetic. This is not a proof-assistant formalization.

The additional program `global_falsification_checks.py` completed 19 deliberate rejection exercises against this exact frozen source manifest. Missing/duplicate cover boxes, a pending box, an incorrect shift, false Gamma/L exclusions, zero residual bounds, path traversal, an incorrect halfwidth, duplicated/out-of-range low indices, mismatched witness metadata, nonfinite or excessive witness values, and a wrong matrix shape were all rejected. Two tests reached the actual exact matrix computation: a well-formed all-zero witness failed `low_basis_rank`, and an intact witness paired with a false zero norm bound failed `F_norm`. The output `global_falsification_checks.json` records each exception and binds the run to the frozen manifest. These tests are supplementary falsification attempts, not substitutes for the all-2,056 acceptance run or the mathematical range argument.
