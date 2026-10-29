# H1 audit and PEC convention

## Scope and current disposition

This file audits only the supplied period-20 bulk-gap premise H1 and the finite PEC convention proposed by the main proof. It does not establish H2, H3, R5, or the general Maxwell reduction. The complete regenerated matrix-check status and runtime records are in `reproduction_summary.json` when that file exists; absence of that file means the full computational reproduction remains unfinished.

The canonical atomic replay has now completed successfully: `work/bulk/clean_certificate/verification_atomic_final/reproduction_summary.json` records all 604 fresh full matrix acceptances, all 11 reconstructed shards, complete independent geometry coverage, and UBSan on every matrix check. Runtime was 280.261 seconds with six workers. A copy of the terminal summary is `results/bulk/h1_reproduction_summary.json`. The immutable original evidence manifest remains SHA-256 `f8c0625768ec5c7705408325d49e010195790379b65096b8fb65231543542de0`; the added atomic driver has SHA-256 `01ae31c516e926e7a87a1b56f5d9dcd0f8ee38532fe12bf3bbe5d58fc89d7771`.

The earlier append-log replay in `verification_final/` is rejected evidence: its shard metadata did not agree with the required number of actual point records. The canonical replay uses one closed atomic file per point, immediate content/hash readback, reconstruction and rereading of every aggregate, and the unchanged fail-closed finalizer. Its terminal marker is `ATOMIC_ALL_604_FULL_REPRODUCTION_COMPLETE`. No claim here rests on the rejected aggregate.

The supplied source is unchanged under `maxwell_research/supplied/`. Working copies and newly regenerated dyadic witnesses live separately under `work/bulk/`. All computational acceptance uses source compilation and current exact matrix checks. Stored `PASS` text is not an acceptance premise.

## Analytic audit

### Scalar averaging and lattice geometry

The conventional cell has coordinates 0 through 19 in every direction. An electric edge in direction j is anchored at integer coordinates, with midpoint displaced by e_j/2. Its four incident cell centers are obtained by choosing the zero or negative unit offset in each perpendicular direction. Thus the material averaging implemented with positive NumPy rolls is the arithmetic average of the intended four scalar cells. The frequency shift is D/64.

A separate pure-integer implementation enumerates the closed sphere union using minimum modular distances rather than the supplied vectorized nearest-representative formula. It independently recovers 3928 high cells and edge numerators {4,15,26,37,48} over denominator 4. It checks FCC shifts and all 48 signed-coordinate-permutation symmetries, including the affine half-cell correction under reflection.

The primitive translations (20,0,0), (10,10,0), (10,0,10) have determinant 2000. Their Fourier characters can be indexed by q=(n1,2n2-n1,2n3-n1) modulo 20. The twisted FFT multiplies the x-transform by exp(2π i n1(j+k)/20) before the two length-10 transforms, exactly producing this character basis. This is a finite Fourier transform of the discrete operator, not a continuum truncation.

The reciprocal vectors have all-even or all-odd coordinates. The supplied argument that |κ_i|≤1 and Σ|κ_i|≤3/2 exhaust the Voronoi inequalities is valid: even vectors use |m_i|≤m_i²; odd vectors use |q_i|=1+2b_i and Σ|κ_i|≤3/2. Signed permutations then reduce the complete zone to the stated ordered wedge.

### Curl and longitudinal degrees of freedom

For the complex skew cross-product matrix C(d), direct multiplication gives

    C(d) C(d)* = |d|² I − conjugate(d) dᵀ.

Thus its two nonzero singular values equal |d|, and its magnetic null direction is conjugate(d). In particular, estimates of the curl by the Euclidean norm of its symbol remain valid for complex Bloch symbols.

Let T=C D^(−1/2). The positive spectra of T*T and TT* coincide with multiplicity. For a positive eigenvalue λ, T and T* map the corresponding eigenspaces bijectively; inverse maps are T*/λ and T/λ. The zero electric eigenvalues of T*T are below [t−σ,t+σ]. Hence excluding the interval from the magnetic positive spectrum excludes it from the complete normalized electric spectrum, including the longitudinal sector. Since D≥I, congruence by D^(−1/2) does not enlarge the inverse norm. Taking the direct integral over Bloch fibers then proves the infinite lattice inverse bound if all fibers have been covered.

Near Γ, C*C has N longitudinal zeros and the two low q=0 transverse eigenvalues; at Γ the latter also vanish, giving N+2 zeros. All remaining eigenvalues have the stated positive Fourier lower bound. The inequalities a0<t−σ and min(a1,a2)>12(t+σ), combined with I≤D≤12I and min-max comparison, give exactly N+2 negative eigenvalues of C*C−t'D and no zero eigenvalue throughout the Γ cube. No projector at q=0 is needed there.

### Box perturbation and Schur argument

The supplied bounds ||ΔC||≤s and ||ΔC−Σ Δκ_a C_a||≤s²/2 follow from the scalar integral remainders for exp(ix) and sqrt(ΣΔκ_a⁴)≤ΣΔκ_a². The quadratic-form remainder for a fixed block F is bounded by s²(||F|| ||C0*F||+||F||²).

The projector remainder is derived directly for center-transverse columns. The variable projector is block diagonal in Fourier index, so Fourier low/high coordinate projectors commute with it. This is essential for the high-block inverse estimate. The stated projector remainder and its high-mode monotone enlargement are valid. The mixed positive/gradient derivative implemented with the raw derivative of the old gradient column is valid after compression by F_+*: its omitted component is parallel to the old gradient and is annihilated by F_+*.

The high block is bounded below by separate positive transverse and longitudinal weights. Inversion reverses that positive-definite order. The transverse shifted-to-center weight ratio decreases as the Fourier radius increases; the derivative numerator has the stated negative terms. The exact identity P Q A F=(2t−t') P Q F controls the longitudinal part separately. Adding an upper bound that includes extra longitudinal contribution to the transverse residual can only enlarge the final Schur bound.

After eliminating the positive high block, the negative block becomes more negative. The physical-positive and gradient blocks remain jointly positive when their two diagonal lower bounds p,g are positive and pg>e². Eliminating the negative block adds a positive-semidefinite correction to this positive block. The four scalar tests therefore imply invertibility of the entire auxiliary matrix. The center-transverse low columns have dimension 2*n_low and interval-certified full rank; the n_low gradient columns and all high coordinates complete a basis. No coordinate sector is omitted.

### Row-sum bound and shifted decay

Each infinite curl row and column has four unit entries. Thus ||C*C||_1,∞≤16. Its diagonal is 4; subtracting D/64 with D≤25 leaves that diagonal positive and decreases the absolute row sum. The same bound applies to the finite PEC convention below. The supplied finite-stencil weighted-resolvent argument then gives its conservative exponential upper decay, conditional only on the audited gap. This is an upper bound, with no implication of H3's lower transmission estimate.

## Independent exact cover check

`independent_checks.py` checks all 16³ rank-4 dyadic voxels in [0,1]³. It tests wedge intersection by enumerating intersections of every three boundary planes of the bounded rational polytope and checking all halfspaces using exact fractions. This differs from the supplied greedy minimal-coordinate feasibility algorithm. Every nonempty voxel outside the Γ cube has a supplied certificate box, and the number required is exactly 604. This checks the geometry of coverage independently; it does not replace the 604 matrix acceptance checks.

## Interval kernel audit

The C++ interval type denotes a complex rectangle with centers x/2^52,y/2^52 and a common radius r/2^52. Every construction used by the accepted records has r≥0. Dyadic input witnesses are bounded and finite; low indices and array shapes are explicitly checked before the C++ calls by the reproduction driver.

For multiplication, the center errors in either real or imaginary part are bounded by

    (|a_x|+|a_y|) b_r + (|b_x|+|b_y|) a_r + 2 a_r b_r,

before division by 2^52. Rounding centers toward zero incurs less than one final integer unit, so outward ceiling plus one is valid. The kernel enforces |center|+radius<2^62. Writing R=2^62, the total radius numerator is at most 2R(r+s)−2rs≤2R²<2^125; real and imaginary product numerators are also below 2^125 in absolute value. These fit signed 128-bit intermediates. Gram accumulation checks signed overflow on every addition; it never relies on a potentially overflowing unchecked sum. Its denominator shift is at most 52+70=122 bits.

Rational scaling uses 64-by-64 products in signed 128-bit integers and outward rounding. Real division enumerates numerator/positive-denominator endpoints with mathematically signed floor and ceiling, so it encloses both signs of the numerator. The target denominators are exactly real (norm squares, real Hermitian pivots, and real positive weights); ignoring their rectangular imaginary uncertainty is valid because their exact real nature is known from the expression. Division products are bounded by fewer than 117 bits before division. Square roots are computed with an integer bit-pair square-root routine and outward endpoint correction; all squared scaled endpoints here fit unsigned 128-bit arithmetic, and their square roots fit signed 64-bit integers.

The PSD checker is interval LDL elimination on the lower triangle of an exactly Hermitian target. Every accepted real pivot has positive lower bound. The upper-triangle interval entries and diagonal imaginary enclosures are unnecessary because Hermitian symmetry is an exact identity of the target. Failed or overflowing elimination returns failure; it is not converted into acceptance.

The Python layer uses arbitrary-size integer dyadic endpoints. Its multiplication takes all four endpoint products. Division excludes zero denominators and takes all endpoint ratios. Pi is enclosed by Machin's identity and alternating-series remainder. Trigonometric arguments are reduced to magnitude less than 4; the factorial Taylor remainder used is conservative for both sin and cos. FFT normalization uses outward square-root and division intervals. Floating operations define or propose witnesses and bounds only; every claimed inequality is subsequently checked on those exact dyadics.

`kernel_endpoint_checks.py` performs 8,000 primitive calls over broad signs, radii, and magnitudes. It compares their enclosures to independently calculated exact Fraction corners and squared square-root endpoints. The tested wrapper is compiled with undefined-behavior sanitization and no recovery. These adversarial tests supplement the general derivation; they are not presented as proof-assistant verification.

### Defensive issues and their disposition

The supplied point checker did not validate all low-index ranges or raw witness shapes before passing arrays into C++. The added driver verifies distinct integer low indices in [0,2000), exact expected array shapes, finite entries, and magnitude bounds. These checks avoid invalid-memory behavior on malformed evidence. They do not alter any mathematical bound.

The supplied cover checker by itself reads stored acceptance records. It is therefore not a standalone matrix verifier. The new reproduction path first recomputes every full matrix certificate, writes fresh records, and only then invokes the supplied cover checker. Its independent cover implementation does not read stored PASS fields.

No formal proof assistant was used. The trusted computational base is the Python integer/Fraction implementation, NumPy's representation and array plumbing, the inspected C++ interval code, the C++ compiler/runtime, and ordinary hardware arithmetic. The acceptance arithmetic does not trust SciPy eigensolvers.

## Finite rectangular PEC convention

Let the physical cell box have side counts Lx,Ly,Lz. Its relative electric edges are

    E_x: 0≤i<Lx, 1≤j<Ly, 1≤k<Lz,
    E_y: 1≤i<Lx, 0≤j<Ly, 1≤k<Lz,
    E_z: 1≤i<Lx, 1≤j<Ly, 0≤k<Lz.

Tangential boundary electric edges are removed, which imposes PEC. Retain all oriented face rows of the closed cubical box, including any all-zero boundary rows. For each active edge, all four incident faces remain. Consequently each column of C has four ±1 entries and diag(CᵀC)=4. Every face has at most four retained boundary edges, so each electric row's sum of absolute off-diagonal contributions is at most 12. For scalar material in [1,25] and t=1/64,

    ||CᵀC−tD||_1,∞ ≤ 16,

because the new diagonal is 4−t ε_edge>0. Every retained edge also has all four incident physical cells; no ghost-cell averaging rule is needed. A uniform scalar increment u/t in every cell shifts every electric diagonal by exactly u.

The finite CᵀC is the principal compression of the infinite Yee stencil to these retained electric edges. Every face incident to a retained edge is present in the finite curl, so no diagonal or local incidence contribution is lost. This fact supplies the needed local agreement away from the outer boundary; it does not assert that the finite compression inherits the infinite spectral gap.

`pec_convention_check.py` independently builds signed face-edge incidences for all 27 boxes with side counts in {2,3,4} and verifies the stated diagonal, row-sum, and four-cell facts in exact integers. The proof above applies to arbitrary side counts.


### Complete integer-range inventory for the acceptance path

All scalar interval radii originate nonnegative and remain so. The final acceptance wrapper explicitly rejects malformed arrays and the signed-minimum absolute-value corner. Compilation retains C++ assertions and Python assertions; `-O2` does not define `NDEBUG`, and the command does not include `-DNDEBUG`.

- `add`, `sub`, `neg`, and conjugation promote 64-bit centers and radii to signed 128-bit before arithmetic. Their intermediate magnitudes use at most 65 bits. Conversion back to 64 bits is range checked. `ab` rejects INT64_MIN before negating it.
- In `mul`, the enforced bounds |a_x|+a_r, |a_y|+a_r, |b_x|+b_r, |b_y|+b_r < 2^62 imply |a_x|+|a_y| < 2^63 and likewise for b. Thus even the source's 64-bit sum inside its radius formula is safe. Each product-center or radius numerator has magnitude below 2^125. Outward quotient conversion is checked.
- In rational scaling, two signed-64-bit magnitudes multiply to less than 2^126. Denominators are positive; INT64_MIN multipliers are rejected by `ab`. The output conversion and final radius increment are checked.
- In positive-real division, m±r has magnitude below 2^64. Multiplication by 2^52 therefore needs fewer than 117 bits. Denominator endpoints are between 1 and 2^64−2. The signed floor/ceiling quotients and differences used to enlarge the output radius also fit signed 128-bit; final conversion is checked.
- A square-root input satisfies 0≤r≤x≤INT64_MAX. Its scaled upper endpoint is below 2^116. The integer square root is therefore below 2^58, so the unsigned-to-signed casts, upper-endpoint increment, midpoint, and endpoint differences cannot overflow signed 64-bit. The bit-pair square-root routine starts with a power of four at most 2^114; its running `res` and `bit` sum remains below 2^116 by summing the geometrically shrinking update terms. The final hardened kernel additionally checks the integer square-root defining inequalities directly with unsigned 128-bit products.
- In `cprod`, each summand has magnitude below 2^125. The 6000-row sums need not satisfy an a priori 128-bit bound: instead, every addition uses `__builtin_add_overflow`, and overflow aborts acceptance. The denominator is 2^(52+power), with 0≤power≤70, hence at most 2^122 and representable. Its quotient-to-64-bit conversion is checked.
- The PSD matrix order is at most 30 for these records. All `n*n` and row/column index products fit 32-bit integers. Pivot divisions use positive real intervals. Every arithmetic primitive continues to enforce the preceding bounds; overflow returns failure or aborts the verifier. No overflow path yields PASS.
- Fourier arrays have 2000 points, three components, and at most 30 columns, so the largest flattened point/column index is below 180000. The FFT's local arrays have length 20, while recursion uses lengths 20,10,5,2,1 as appropriate to the supplied mixed radix. Every root index lies in [0,19]; phase products i(j+k) are at most 342. Face/edge averaging denominators lie in {4,15,26,37,48}.
- The Python wrapper's PSD rescaling exponent is at most 52 and at least −11 for nonzero valid 64-bit interval data, so its integer rational scale factors fit signed 64-bit. The 100-bit scalar layer uses unbounded Python integers. Its deliberate conversion to 52-bit C++ intervals is checked by the NumPy dtype conversion and the preceding fixed parameter ranges; all relevant centers are bounded by the supplied constants and representable. The only in-place NumPy center addition is the +2^52 restoring a root-of-unity value from d_j; |d_j|≤2 makes this far smaller than 2^63.

The final clean check uses undefined-behavior sanitization for every matrix certificate as an additional runtime check. This does not replace the bounds above or establish correctness of the compiler/hardware.
