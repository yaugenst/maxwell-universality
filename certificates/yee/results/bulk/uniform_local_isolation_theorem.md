# Certified uniform two-band isolation near every L point

## Statement

Let H0(k)=C(k)*C(k)−D/64 be the exact period-20 diamond Yee operator from the supplied bulk-gap theorem. Let L range over its symmetry-related FCC L points, and write k=L+q in Cartesian reciprocal coordinates. For every ||q||∞≤1/20,

1. H0(k)−(7/256)I has spectral distance at least 1/4096 from zero and exactly 2004 negative eigenvalues in the 6000-dimensional primitive electric fiber;
2. H0(k) has exactly 2002 negative eigenvalues and spectral distance at least 1/4096, using the independently replayed H1 premise;
3. therefore H0(k) has exactly two positive eigenvalues below 7/256.

The first item is established by a fresh exact interval full-matrix certificate, not a numerical band sample. The second remains conditional on completion of the separate H1 replay until its final summary exists. The supplied H1 theorem's analytic proof and the replay are documented separately.

Let scalar cell increments satisfy 0≤δc≤1023/2^20 and retain FCC periodicity. Arithmetic four-cell averaging gives 0≤δD≤(1023/2^20)I. Put Hpert=H0−δD/64 and

    g = 1/4096 − 1023/2^26 = 15361/2^26 > 0.

Then throughout each same cube (and hence the Euclidean ball of radius1/20), exactly two positive eigenvalues of Hpert lie in (0,7/256). All negative eigenvalues are at most −g; the two isolated positive eigenvalues lie between g and7/256−g; every other positive eigenvalue is at least7/256+g.

For z in I=[239/25000,957/100000]=[0.00956,0.00957], if P(k) is the orthogonal projection onto these two positive eigenvalues, then

    dist(z, spec(Hpert(k) restricted to Ran(I−P(k)))) > 1/128.

Thus the instantaneous complementary resolvent has norm less than128 uniformly on these neighborhoods. This is not a bound for the compression onto a fixed center eigenspace's orthogonal complement; that separate obligation has not been discharged here.

## Exact matrix certificate and its extension

At L=(1/2,1/2,1/2), set D'=D+(7/4)I. Then

    C*C−D'/64 = H0−(7/256)I.

D' has scalar cell values11/4 and55/4, and edge values obtained by the same four-cell average. Hence D'≤14I. Its inverse edge material is exactly 4/(old_four_cell_sum+7), which is the arithmetic used by the verifier.

The original magnetic/Schur certificate applies without a special restriction to two negative columns. Here the exact negative basis has four columns. The low Fourier transverse columns, low gradient columns, and all high Fourier coordinates still form a complete basis. The exact verifier proves the four-column negative compression, complementary positive compression, low-basis rank, every center operator norm, derivative norm, weighted residual norm, and all interval box inequalities.

The operating squared frequency is t=1/64. The certified box has the exact binary halfwidth represented by Python float0.05, which is slightly larger than1/20. The proof therefore covers the claimed rational cube. The verified squared-frequency interval is

    t' ∈ [1/64−1/4096, 1/64+1/4096].

The same full-box proof excludes nonzero magnetic eigenvalues from that interval. The positive spectra of C D'^(−1) C* and D'^(−1/2) C*C D'^(−1/2) coincide with multiplicity. The zero normalized electric spectrum is below the interval. Since D'≥I, congruence gives

    ||(C*C−D'/64)^−1|| ≤4096.

The auxiliary magnetic operator has exactly four negative eigenvalues. The electric normalized matrix has2000 longitudinal eigenvalues below the operating frequency in this neighborhood, so the shifted electric inertia is2004 negative eigenvalues. Original cubic scalar geometry symmetries transfer the certificate to every L point and rotate its cube. The Euclidean radius1/20 ball is contained in each rotated cube. No symmetry of the perturbation is required for the norm-bounded perturbation step.

## Perturbation transfer

The material perturbation has electric operator norm at mostδ=1023/2^26. Both original gaps (at0 and at7/256) exceedδ. Hermitian eigenvalue perturbation bounds therefore preserve the counts2002 and2004 at those two thresholds. This proves that exactly two eigenvalues lie between them and supplies the displayed endpoint marginsg.

For z∈I, the negative complementary spectrum is separated by at least239/25000+g and the higher complementary spectrum by at least7/256+g−957/100000. Direct rational comparison shows both exceed1/128. This proves the resolvent bound by the spectral theorem.

## Evidence and reproduction

Work directory: `work/bulk/edge_isolation/` relative to the research root.

Run from that directory:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python verify_uniform_local_isolation.py

The command compiles the exact interval kernel with undefined-behavior sanitization, checks all center matrices afresh from the untrusted dyadic NPZ witness, verifies the full box directly atσ=1/4096, checks witness hashes before and after acceptance, and writes `uniform_local_isolation_acceptance.json`. Missing or invalid witness data raises. It uses NumPy for array representation; floating eigensolvers are not used in acceptance.

Primary output: `uniform_local_isolation_acceptance.json` and `uniform_local_isolation.log`. Source: `verify_uniform_local_isolation.py`, `verify_point.py`, `interval_tools.py`, `interval_kernel.cpp`, and `exact_geometry.py`. Input: `upper_7over256_proposal.json` and `witnesses/upper_7over256.npz`. The exact generated full-box witness is `witnesses/upper_7over256_full_box.npz`.

The preceding exploratory bracket certificates at1/256,5/256 and3/128 are retained but are not needed for this stronger uniform assertion.

## Limitations

This establishes a two-band spectral cluster throughout a fixed L neighborhood. It does not prove that its lower eigenvalue attains its minimum only at L, that its Hessian stays positive on the neighborhood, that the four L minima have different heights, or that a fixed-center Feshbach complement remains invertible. It also does not establish global exclusion away from these neighborhoods. Those are separate edge/coupling obligations.
