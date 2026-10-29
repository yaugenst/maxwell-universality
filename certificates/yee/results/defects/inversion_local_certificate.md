# Exact local band-edge certificate for the inversion-symmetric FCC candidate

## Result and scope

The finite certificates in this directory establish the following result,
when combined with the independently accepted bulk inertia certificates and
the polynomial-neighborhood lemma in `results/main/local_edge_polynomial_lemma.md`.

For the explicitly specified scalar-cell material below, each of the four
inequivalent FCC L points is a simple strict local minimum of the lower
positive electric band. Throughout its Cartesian reciprocal-coordinate
ball of radius `1/20`, both positive bands lie strictly above the lower
band's value at the center, except for that lower value at the center
itself. More precisely, if `E_L` is the lower value at L, then

\[
 \lambda_{\rm low}(L+q)-E_L>|q|^2/600,
 \qquad 0<|q|\le 1/20.
\]

The lower value at `L++-=(1/2,1/2,-1/2)` is strictly smaller than the lower
values at the other three centers, by more than `33/10^9`.

**This document does not certify the global minimum outside these four
balls.** The separate whole-Brillouin-zone comparator cover is the remaining
spectral-edge obligation. The local assertions above do not use a sampled
Hessian or a sampled directional test as an acceptance criterion.

## 1. Exact scalar material

The period is 20. The FCC primitive lattice has basis

\[
 (20,0,0),\quad(10,10,0),\quad(10,0,10),
\]

and 2000 cells represented by `(x,y,z)` with `0<=x<20` and `0<=y,z<10`.
The electric Bloch matrix has dimension 6000. The unperturbed diamond
material takes scalar cell values 1 and 12. Membership is reconstructed
from integer squared distances, using doubled cell centers and the exact
closed-ball inequality; the superseded floating geometry is not used.

The candidate is

\[
 \varepsilon(c)=\varepsilon_0(c)+p_c/2^{21},
 \qquad 0\le p_c\le2046.
\]

The complete 2000-entry primitive list, the full 20-by-20-by-20 integer
table, their ordering and the lattice are frozen in
`inversion_edge_material.json`. Every acceptance script compares its
witness table with this same canonical full table before doing arithmetic.
The numerical generator originally formed
the perturbation by symmetrizing a fixed integer array, but the saved
integer list itself defines the material; no random-number generator is
part of the mathematical specification.

The exact checker verifies FCC translation invariance and

\[
 p_{-c-\boldsymbol1}=p_c.
\]

Each electric edge receives the arithmetic mean of its four incident
scalar cell values. At `t=omega^2=1/64`, the perturbation of the electric
operator has norm at most

\[
 \rho=1023/2^{26}<1/4096.
\]

Thus the already certified original gap at zero persists, with gap at
least `1/4096-rho`. All cells remain between 1 and `12+1023/2^20`.

## 2. Point inclusion, simplicity, and common inversion parity

At an L point all primitive Bloch phases are signs. The finite curl and
the diagonal mass are reconstructed exactly with integers; the common
denominator of the mass term is `2^29`.

For an electric edge of direction `j` anchored at `r`, polar-vector
inversion sends it to the edge anchored at `-r-e_j`, with the usual minus
sign and the primitive-lattice Bloch sign. This gives an exact signed
permutation `I`. The checker verifies `I^2=1` and `[I,A(0)]=0`.

Floating eigenvectors are only witnesses. They are converted to dyadic
vectors and projected **exactly** to one inversion sector. Their Rayleigh
centers and squared residuals are recomputed with integers. The accepted
intervals each have radius at most `2^-47`. For each L point the two
intervals are disjoint and their total span is less than `2^-20`.

The accepted parity is `-1` at `L+++`, and `+1` at each of `L++-`, `L+-+`,
and `L-++`. Common parity within a pair is the property required below;
the parity need not agree between different L points.

The separately accepted original-crystal inertia certificates at electric
shifts `1/256` and `5/256` prove that there are exactly two electric
eigenvalues between these shifts at an original L point. Cubic symmetry
of the original material transfers this count to all four original L
points. Weyl's inequality under the nonnegative scalar perturbation then
leaves exactly two perturbed eigenvalues in the tracked region

\[
 I_*=[239/25000,\,957/100000]=[0.00956,0.00957],
\]

with complementary spectral distance greater than

\[
 \gamma=11/2000.
\]

The disjoint residual intervals each contain an eigenvalue in the stated
inversion sector. Since the entire cluster has dimension two, they are
simple and exhaust the cluster. In particular the exact cluster lies
entirely in its certified parity sector.

The checker `verify_inversion_point_residuals.py` accepts these residual,
parity, ordering, and scalar Weyl-transfer facts. Its acceptance record is
`inversion_point_residual_acceptance.json`. The original interval-inertia
proofs are independent dependencies, not inferred from the existence of
approximate eigenvectors or from a JSON status flag.

## 3. Centered gauge and integer derivative matrices

Let `q` denote displacement from L in Cartesian reciprocal coordinates,
with physical phase convention `exp(2 pi i q.r/20)`, and put
`alpha=pi/20`. In an electric-edge/face-center gauge, each directional
curl difference is

\[
 D_j(q)=S_j e^{i\alpha q_j}-I e^{-i\alpha q_j},
\]

where `S_j` is the exact signed shift at L. In this gauge inversion is
constant and satisfies `I A(q) I=A(-q)`.

For completeness, this identity holds for all `q`, not only for the
first two derivatives checked by the program. An electric field in the
fiber has translation character `chi_L(T) exp(2 pi i q.T/20)`. Remove
the factor `exp(2 pi i q.(r+e_j/2)/20)` at each electric edge center.
When inversion reduces `-r-e_j` to a primitive representative plus `T`,
the translation's `q` character cancels against the two center factors.
Only the fixed TRIM sign `chi_L(T)` and the polar-vector minus sign
remain. The face-center gauge has the corresponding axial-vector action.
Curl covariance and the exact inversion symmetry of the scalar material
then give `I A(q) I=A(-q)` identically.

There are real integer matrices `B_i` and `D_ij` such that

\[
 A_i=i\alpha B_i,\qquad A_{ij}=\alpha^2D_{ij}.
\]

Here `B_i` is antisymmetric and `D_ij` is symmetric. The integer checker
verifies that the `B_i` reverse parity, the `D_ij` preserve parity, and
their absolute row sums bound their operator norms by 8 and 12,
respectively. The matrices are rebuilt from incidence operations, not
read as rounded derivative arrays.

## 4. Rigorous passage from witness vectors to the exact cluster

Write `U` for the dyadic 6000-by-2 witness matrix and `Z` for its two
dyadic Rayleigh centers. The checker establishes

\[
 \|AU-UZ\|_F\le10^{-13},\qquad
 \|U^*U-I\|\le10^{-12}.
\]

Let `P` be the exact two-mode spectral projection. The complementary gap
gives

\[
 \|(I-P)U\|\le10^{-13}/\gamma.
\]

Polar normalization of `PU` gives an exact orthonormal cluster basis
`Phi` with

\[
 \|\Phi-U\|<10^{-10}.
\]

This follows, for example, by bounding the Gram error of `PU` by
`10^-12+(10^-13/gamma)^2` and the polar correction by twice that quantity.
Because `P` and `I` commute and the witness columns have common exact
parity, `Phi` has that same parity.

Let `E` be the exact lower cluster eigenvalue. Its distance from the
lower dyadic Rayleigh center `z` is explicitly checked to be less than
`10^-13`, using the **normalized** residual interval. The exact operator
`Phi^*(A-E)Phi` is positive semidefinite with eigenvalues `0,delta`, where
`0<delta<2^-20`. It may be diagonalized by an internal two-dimensional
unitary without changing any of the norm or finite block inequalities.

## 5. Opposite-parity solves and Hessian enclosure

The opposite-parity restriction of `A-E` excludes the entire two-mode
cluster and has inverse norm at most `1/gamma`. This avoids division by
the small internal doublet splitting.

The checker converts the floating derivative solves to dyadic real
matrices `y_i`, projects them exactly to the opposite parity, and verifies

\[
 \left\|\big[(A-z)y_i-B_iU\big]_{i=1}^3\right\|_F
 \le2^{-35}.
\]

The physical exact derivative columns are

\[
 Y_i=(A_{\rm opposite}-E)^{-1}A_i\Phi.
\]

All entries of the two-mode Feshbach Hessian are enclosed from the exact
rational witness expression

\[
 \alpha^2\{U^*D_{ij}U-(B_iU)^*y_j-(B_jU)^*y_i\}.
\]

Bounds for pi are proved by Machin's identity and alternating rational
arctangent bounds, then rounded outward to 25 decimal places. Error
budgets separately account for the cluster basis, solve residual, energy
center, and rational rounding.

For the energy term the decomposition holds `Phi` fixed while changing
the resolvent energy from `E` to `z`; it then changes `Phi` to `U` at `z`.
Thus the energy term uses the norm-one exact basis and does not need an
extra witness-Gram factor. In the alternative decomposition used for the
linear residual vectors, the energy change holds `U` fixed and includes
the required bound `||U||<=1+10^-12`.

An entrywise error of `10^-5` is ample: the actual common bound is below
`1.3*10^-7`. Exact rational LDL tests certify, at **all four** L points,

\[
 \frac1{25}I_6<\mathcal H<I_6,\qquad
 \|[Y_1\;Y_2\;Y_3]\|<291/100<3.
\]

Here the `ij` block of `mathcal H` is the two-by-two Feshbach Hessian
block. Consequently its compression to `q tensor x` gives

\[
 \frac1{50}|q|^2I<K_2(q)<\frac12|q|^2I.
\]

These are actual matrix inequalities, not directional samples.

## 6. The full quadratic residual Gram certificate

Define exact matrices

\[
 T_{ij}=\tfrac12(A_{ij}\Phi-A_iY_j-A_jY_i),\qquad
 R_2(q)=\sum_{ij}q_iq_jT_{ij}.
\]

Let `G` be the six-by-six block Gram matrix with blocks

\[
 G_{jk}=\sum_i T_{ij}^*T_{ik}.
\]

In integer witness units the numerator for `T_ij` is

\[
 D_{ij}U+B_iy_j+B_jy_i,
\]

with the common factor `alpha^2/2`. The plus signs result from the two
factors of `i` in `A_iY_j`; this is also checked against the defining
incidence derivatives.

The rational checker bounds the change in each `T_ij` from witness to
exact basis/energy, bounds the full block matrix change by three times
that block bound, and uses

\[
 \|(W+\Delta W)^*(W+\Delta W)-W^*W\|
 \le(2\|W\|+\|\Delta W\|)\|\Delta W\|.
\]

An exact LDL test with a `1/10000` margin proves

\[
 G\le\frac{18}{5}\frac{\mathcal H}{2}.
\]

The total certified comparison error is less than `1.8*10^-6`. By
Cauchy-Schwarz in the first spatial index,

\[
 \|R_2(q)x\|^2
 \le\frac{18}{5}|q|^2x^*K_2(q)x.
\]

This is the full quadratic residual, not only its component orthogonal
to the center eigenspace.

## 7. Whole-ball conclusion and dependencies

The independent bulk certificate at electric shift `b=7/256` passes the
full Cartesian box of halfwidth `1/20` with a frequency interval that
implies an electric gap at least `1/4096`. The scalar perturbation norm
is smaller than this gap. Together with H1 at zero, inertia therefore
proves that each perturbed L ball contains exactly two positive bands in
`(0,b)` and that all other eigenvalues are outside `[0,b]`.

The hypotheses of `results/main/local_edge_polynomial_lemma.md` now hold
at every L point. That lemma tests

\[
 g_E(A)=(A-E)(b-A)
\]

on the exact trial space `F(q)=Phi-sum q_iY_i`. Its constant term is the
exact positive semidefinite matrix
`Delta((b-E)I-Delta)`; no approximate residual is inserted as a constant
error near `q=0`. Inversion cancels the odd cross terms. The independent
scalar verifier `results/main/verify_local_edge_scalar.py` proves the
remaining radius-`1/20` inequality. Hermitian min-max then forces both
positive bands above `E`, with the quantitative bound stated at the
start of this document.

## 8. Replay and files

Run from the unpacked research root (the directory containing `results`,
`work`, and `supplied`):

```bash
python results/defects/verify_inversion_point_residuals.py
python results/defects/verify_inversion_feshbach_curvature.py
python results/defects/verify_inversion_feshbach_curvature.py --stem inversion_feshbach_lppp
python results/defects/verify_inversion_feshbach_curvature.py --stem inversion_feshbach_lpmp
python results/defects/verify_inversion_feshbach_curvature.py --stem inversion_feshbach_lmpp
python results/main/verify_local_edge_scalar.py
```

The verifiers fail immediately under Python optimization, so `-O` or
`PYTHONOPTIMIZE` cannot silently remove the acceptance assertions.

The four exact finite matrix acceptance records are
`inversion_feshbach_curvature_acceptance.json` (L++-),
`inversion_feshbach_lppp_curvature_acceptance.json`,
`inversion_feshbach_lpmp_curvature_acceptance.json`, and
`inversion_feshbach_lmpp_curvature_acceptance.json`.

The `.npz` arrays are witnesses. They need not be trusted: the exact
checker recomputes their residuals, parity, derivative contractions,
error budgets, and rational LDL acceptance. The exploratory generators
and their sampled diagnostic numbers remain explicitly labeled numerical.
The original interval-inertia verifiers must also be replayed to check
the independent spectral-isolation dependencies.
