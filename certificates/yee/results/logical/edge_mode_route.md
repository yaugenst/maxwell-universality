# A simple admissible defect mode near a regular three-dimensional band edge

## Status and precise scope

This is an analytic conditional theorem. It replaces the generic-supercell
perturbation in the earlier H2 argument by a band-edge construction that
preserves the original periodic background up to a uniform scalar shift.
Its useful extra conclusion is a defect mode with nonzero overlap with the
edge Bloch mode, and hence nonzero analytic numerators at any nearby complex
critical points used in a subsequent Green-function asymptotic.

The problem-specific premise is a **certified admissible periodic Yee
background with a unique simple nondegenerate TRIM minimum at the bottom
of a complete upper band**, with material headroom. For the actual
inversion-FCC background, that premise is now proved by the finite
certificates assembled in `../../theorem_and_proof.md`, Section 8, and
`../main/global_edge_assembly_audit.md`. H1 alone would not suffice.
The full directional resolvent estimates are separately proved in
`../main/discrete_edge_green_lemma.md`. The current all-dependency replay
and overall completion status remain recorded in `../../obligations.md`.

Everything below concerns the discrete operator. No continuum statement,
finite-PEC-box spectral gap, or complex physical material is asserted.

The spectral distance from the edge is denoted xi>0, to distinguish it from
the physical cell permittivities and from the eventual solver tolerance.

## 1. Conditional band-edge data

Group the electric edges of the infinite periodic Yee lattice into period
cells indexed by n in Z^3. There are d electric coordinates per period cell.
Use an anchor Bloch gauge in which

    H_0(k) = sum_a H_a exp(i k dot a),     k in T^3,

is a finite Hermitian Laurent-polynomial matrix for real k,
H_0(-k)=conjugate(H_0(k)), and H_0(k)^T=H_0(-k). The coefficient matrices
are real and satisfy H_a^T=H_-a. This gauge exists for a real finite-stencil
periodic operator and does not change the physical material convention.

Assume the following certified data for

    H_0=C_Yee^T C_Yee-t D_b,       t=omega^2>0.

1. **Admissible scalar background.** The cells of epsilon_b are dyadic,
   periodic, and at least one. The frequency and grid satisfy the fixed
   amended-class sampling inequality. For some known rational h_mat>0,

       max epsilon_b + E_*/t <= 25-h_mat.                  (1.1)

2. **Complete lower gap.** E_*>0 is the bottom of an upper spectral band.
   Every spectral value of every real Bloch fiber is either at most
   E_*-g_- or at least E_*, for a known rational g_->0.

3. **Unique simple edge.** Equality to E_* occurs only at one point k_*
   of the Bloch torus; k_* has coordinates in {0,pi}. The fiber eigenvalue
   E_* at that point is simple.

4. **Positive quadratic dispersion.** Writing k=k_*+q near zero, the
   corresponding analytic eigenvalue has

       E(k_*+q)=E_*+d(q),
       d(q)=q^T A q+O(|q|^4),       A positive definite.    (1.2)

   Certified rational constants a_0,a_1,M_4,r_0>0 can be supplied with
   a_0 I<=A<=a_1 I and

       |d(q)-q^T A q|<=M_4 |q|^4,
       (a_0/2)|q|^2<=d(q)<=d_max |q|^2                    (1.3)

   for |q|<=r_0, where d_max may be taken as 2a_1 after reducing r_0.
   All other bands in this ball, and all bands outside the ball, have a
   certified positive distance from E_*.

The last separation follows from the qualitative assumptions by
compactness; its effective certificate is part of the intended band-edge
data. The quartic rather than cubic remainder in (1.2) follows from
time reversal at a TRIM: simplicity gives E(k_*+q)=E(k_*-q).

At a TRIM, the anchor-gauge matrix H_0(k_*) is real symmetric. Let phi_*
be its real unit eigenvector at E_*. Its extended Bloch field is

    Phi_*(n)=exp(i k_* dot n) phi_*.

This is real because the Bloch signs are +/-1. It has squared norm one
per period cell and is not an ell^2 vector.

The simple eigenprojection P(q) and a normalized eigenvector phi(q) can
be chosen analytically for real q near zero, with phi(0)=phi_*, and

    ||phi(q)-phi_*||<=C_phi |q|.                           (1.4)

All local derivative bounds are effective from a finite fiber gap and
the Laurent coefficients. For example, on a sufficiently small complex
polydisk the resolvent on a fixed contour about E_* has a convergent
Neumann series. Its contour integral supplies an analytic rank-one Riesz
projection; Cauchy estimates bound its derivatives. A local analytic
normalization of P(q)phi_* supplies (1.4). This argument does not assume
any global complex-band theorem.

## 2. Scalar defect and finite compressed resolvent

Let D be any fixed finite set of scalar cells. Let Q select all affected
electric edges and W be the diagonal matrix of their changed incident-cell
fractions. Thus W_ee is in {1/4,1/2,3/4,1}, and changing every scalar cell
in D by v/t changes the operator by -v Q^T W Q. Define

    K=Q^T W^(1/2),           w=K^T Phi_*.

The vector w is well-defined because K has finite support. For
0<xi<g_-/2, put

    H_xi=H_0-(E_*-xi)I,
    S_xi=K^T H_xi^(-1) K.                                 (2.1)

The real spectrum of H_xi lies in
(-infinity,-g_-+xi] union [xi,infinity). In particular its gap is at
least xi, and S_xi is real symmetric. The physical realization of H_xi
is the uniform cell increment (E_*-xi)/t; Section 7 chooses this increment
to be dyadic rather than assuming E_* itself is rational.

The next lemma is special to three spatial dimensions.

### Lemma 2.1: rank-one square-root expansion

For every fixed finite scalar defect support,

    S_0 := lim_(xi downarrow 0) S_xi

exists in finite-matrix operator norm. Moreover,

    S_xi = S_0-c_A sqrt(xi) w w^T + R_xi,
    ||R_xi||<=C_D xi,
    c_A=1/(4 pi sqrt(det A))>0,                            (2.2)

for all sufficiently small xi>0. C_D and the permitted interval are
effectively bounded from the conditional band-edge data and the finite
support. S_0 is a compressed limiting quadratic form; this lemma does
**not** assert that H_0-E_*I has a bounded inverse on the infinite lattice.

#### Proof

Use the unitary Bloch transform with measure (2pi)^(-3)dk. The contribution
of the selected band in the ball |q|<r_0 has the form

    integral B(q)/(d(q)+xi) dq/(2pi)^3,

where B(q) is a finite matrix analytic near zero, positive semidefinite
for real q, and

    B(0)=w w^T,       B(-q)=B(q)^T.

Explicitly, let V(q) map a period-cell vector to its affected-edge values
with phases exp(i(k_*+q) dot n) and weights sqrt(W_ee). Then

    B(q)=V(q) P(q) V(-q)^T.

For real q, V(-q)^T=V(q)^* and P(q) is Hermitian. Time reversal gives
the stated transpose relation. Since d(q) is even and the integration
ball is symmetric, B may be replaced by

    B_even(q)=(B(q)+B(-q))/2.

Its first-order Taylor terms vanish, so

    ||B_even(q)-w w^T||<=M_B |q|^2.                        (2.3)

The remainder of the Bloch integral has denominators bounded away from
zero uniformly; its difference between xi and zero is O(xi). The selected
band is integrable at xi=0 because 1/|q|^2 is locally integrable in
dimension three. Thus S_0 exists.

For the band contribution to S_0-S_xi, the scalar multiplier is

    f_xi(d)=xi/[d(d+xi)].

Replacing B_even by w w^T introduces O(xi): by (1.3) and (2.3), its
integrand norm is bounded by a fixed constant times
xi/(c|q|^2+xi), whose three-dimensional integral is O(xi).

Replacing d(q) by Q_A(q)=q^T A q also introduces O(xi). Indeed

    |f_xi'(x)|
      =xi(2x+xi)/[x^2(x+xi)^2]
      <=2xi/[x^2(x+xi)].

Between d(q) and Q_A(q), x is at least (a_0/2)|q|^2. Multiplication by
the quartic remainder M_4|q|^4 therefore bounds the replacement error
by a fixed constant times xi/(c|q|^2+xi), again integrable with O(xi)
norm. All these bounds also hold at q=0 by taking the integrable limit.

Finally extend the quadratic integral from the fixed ball to R^3. Its
tail is at most a constant times
xi integral_(r_0)^infinity r^(-2)dr=O(xi). The full integral is exact:

    integral_(R^3) xi/[Q_A(q)(Q_A(q)+xi)] dq/(2pi)^3
      = sqrt(xi)/sqrt(det A)
          * integral_(R^3) 1/[|z|^2(|z|^2+1)] dz/(2pi)^3
      = sqrt(xi)/(4pi sqrt(det A)).

Here the radial integral is
4pi integral_0^infinity (1+r^2)^(-1)dr=2pi^2.
Combining the replacements proves (2.2). All error bounds depend on
finite support and certified finite-dimensional analytic bounds, so they
are effective. QED.

## 3. An all-cell cube has a large edge-overlapping Rayleigh quotient

Choose D=D_L to be a scalar-cell cube containing every scalar cell incident
to all electric-edge anchors in L^3 consecutive period cells. Add a fixed
cell margin so this holds under the chosen Yee indexing. One may take a
cube from -2 through PL+2 in each fine-grid coordinate for a cubic period
P. A larger fixed margin is harmless.

For L>=8, the affected coordinates occupy at most (L+8)^3<=8L^3 period
cells, all with translation indices n satisfying |n|<=4L after choosing
the origin. Write W_n for the diagonal fractions in period cell n, using
zero outside the affected set. On the L^3 designated interior period
cells W_n=I. Consequently, with w=w_L,

    a_L:=||w||^2=sum_n phi_*^T W_n phi_*,
    L^3<=a_L<=8L^3.                                       (3.1)

The compact source f=K w has cell components

    f(n)=W_n exp(i k_* dot n) phi_*.

At k_*+q its overlap with the selected band is

    A_L(q)=phi(q)^* sum_n exp(-i q dot n) W_n phi_*.

At zero it equals a_L. By (1.4), positivity of W_n, and the support bound,

    |A_L(q)-a_L|
      <=4L|q| a_L + 8 C_phi L^3 |q|.                      (3.2)

Choose a fixed positive rational

    r_*<=min(r_0,1/64,1/[64(1+C_phi)]).

For |q|<=r_*/L and L>=8, (3.1)-(3.2) imply

    |A_L(q)|>=a_L/2.                                     (3.3)

In fact the displayed choices leave more than this margin. The selected
positive band contributes at least

    (a_L^2/4) integral_(|q|<=r_*/L)
           [1/(d_max |q|^2)] dq/(2pi)^3
      = a_L^2 r_*/(8pi^2 d_max L)

to w^T S_0 w. Every other contribution above E_* is nonnegative. All
bands below E_* have inverse magnitude at most 1/g_-, so their contribution
is bounded below by -||f||^2/g_-. Since ||K||<=1, ||f||<=||w||.
Divide by a_L and use (3.1):

    w^T S_0 w / ||w||^2
      >= [r_*/(8pi^2 d_max)] L^2 - 1/g_-
      >= c_cube L^2 - 1/g_-,
    c_cube=r_*/(80 d_max)>0.                              (3.4)

The last constant is rational and uses pi^2<10. This proves quadratic
growth from a coherent ball in the Bloch integral; it does not infer the
growth from a finite-domain eigenvalue or from numerical quadrature.

For any fixed threshold T>0, choose an effectively computable integer
L>=8 with

    c_cube L^2 - 1/g_->T+2.                               (3.5)

The real symmetric finite matrix S_0 then has an eigenvalue lambda>T+2
such that

    a=P_lambda w !=0,                                    (3.6)

where P_lambda denotes its full orthogonal eigenspace projection. To
prove this, decompose the Rayleigh quotient into the weighted average
sum_lambda lambda ||P_lambda w||^2 / ||w||^2. If all nonzero weights
were at eigenvalues at most T+2, (3.5) would be impossible. No simplicity
of lambda or knowledge of its exact multiplicity is assumed.

## 4. A rank-one square-root perturbation selects a simple branch

The following finite-dimensional lemma addresses possible degeneracy at
the limiting edge. It needs only the norm expansion, not analyticity of
S_xi as a function of sqrt(xi).

### Lemma 4.1

Let S_tau be real symmetric and

    S_tau=S_0+tau B+E_tau,
    ||E_tau||<=C tau^2,
    B=-c w w^T,       c>0.

If S_0 has an eigenvalue lambda with a=P_lambda w !=0, then for all
sufficiently small tau>0 there is a **simple** eigenvalue and real unit
eigenvector satisfying

    mu_tau=lambda-c||a||^2 tau+O(tau^2),
    u_tau=a/||a||+O(tau),
    w^T u_tau=||a||+O(tau)>0.                             (4.1)

Its separation from every other eigenvalue is at least
(c||a||^2/2)tau after reducing the interval. Constants are finite for
this fixed matrix. The eigenvector sign is chosen by w^T u_tau>0.

#### Proof

Let P=P_lambda and Q=I-P. If Q is nonzero, let gamma>0 be the distance
between lambda and the spectrum on Q. Put C_Q=Q(S_0-lambda I)Q. Define
the real skew-symmetric off-diagonal matrix X by

    X_QP=-C_Q^(-1) QBP,
    X_PQ=PBQ C_Q^(-1),
    X_PP=X_QQ=0.

Then [S_0,X] cancels the off-diagonal blocks of B. If Q=0, use X=0.
The orthogonal matrix U_tau=exp(tau X) gives

    U_tau^T S_tau U_tau
      = S_0+tau(PBP+QBQ)+F_tau,
    ||F_tau||<=C' tau^2.                                 (4.2)

For instance C'=C+2||S_0||||X||^2+2||B||||X|| suffices, by integrating
the first and second derivatives of orthogonal conjugation. The formula
has no formal power-series convergence issue.

On P the leading matrix in (4.2) is

    lambda I_P-c tau a a^T.

It has the simple eigenvalue lambda-b tau, where b=c||a||^2>0, with
unit eigenvector u_0=a/||a||. All remaining P eigenvalues equal lambda.
For small enough tau, the Q spectrum remains at least gamma/2 from
lambda-b tau. Also arrange b tau<=gamma/2 if Q is nonzero. The target
eigenvalue is thus separated from the rest by at least b tau. When
C' tau^2<=b tau/4, Weyl's eigenvalue inequalities place exactly one
eigenvalue of the perturbed matrix in its target interval, with separation
at least b tau/2. This eigenvalue is simple.

For its unit eigenvector v_tau in the conjugated basis, projection of
the eigenvector equation onto u_0's orthogonal complement gives

    ||(I-u_0u_0^T)v_tau||<=2C' tau/b.

With the appropriate sign this implies
||v_tau-u_0||<=3C'tau/b. Since
||U_tau-I||<=tau||X||, the original vector obeys

    ||u_tau-u_0||<=(||X||+3C'/b)tau.

Finally w^T u_0=||a||, so the last assertion of (4.1) follows. QED.

Apply the lemma to (2.2), with tau=sqrt(xi), c=c_A, and the eigenvalue
from (3.6). For all sufficiently small xi>0,

    mu_xi>T+1,
    S_xi u_xi=mu_xi u_xi,
    mu_xi simple,
    u_xi -> u_0=P_lambda w/||P_lambda w||,
    w^T u_xi -> ||P_lambda w||>0.                          (4.3)

This selects a useful mode even if the limiting compressed matrix has
symmetry-enforced multiplicity. It does not perturb individual scalar
cells or break the background's spatial symmetry.

## 5. Admissible tuning and physical localization

Take

    T=4/(t h_mat)

in (3.5). By (4.3), v_*=1/mu_xi satisfies

    0<v_*<t h_mat/4.

The gap of H_xi is at least xi, and ||K||<=1, so
mu_xi<=||S_xi||<=1/xi. Thus v_*>=xi. Choose any rational
xi_low in (0,xi] and let delta_v=xi_low/4. For
|v-v_*|<=delta_v,

    v>=3v_*/4>0,
    v<=5v_*/4<5t h_mat/16.

The background after uniform shifting is at most 25-h_mat by (1.1).
Adding the common scalar defect increment v/t therefore leaves the
maximum below 25-11h_mat/16, in particular below 25-h_mat/2. This gives
a fixed two-sided tuning interval and fixed upper material headroom.

The defect changes whole scalar cells, so its electric perturbation is
exactly -v Q^T WQ. Birman-Schwinger algebra gives a one-dimensional
kernel at v=v_*:

    E=H_xi^(-1)K u_xi,
    (H_xi-v_* Q^T WQ)E=0.

The correspondence between this kernel and the eigenspace of S_xi at
mu_xi is injective in both directions. Simplicity therefore gives a
unique physical zero mode up to scaling, regardless of the signs of the
other compressed eigenvalues.

Exponential localization follows from the positive gap xi and finite
stencil. Use bounded weights
exp(a min(dist(edge,supp K),R)), choose fixed a>0 so that the conjugated
operator differs in norm by less than xi/2, bound its inverse uniformly
in R, and take the monotone limit. The physical operator and material
remain real; complex Bloch variables are used only as an analytic tool.

## 6. Nonzero numerator at nearby complex critical points

For a real unit defect vector u, put f_u=K u and let fhat_u(k) be its
finite Fourier/Bloch polynomial. On the simple edge band define the
analytic scalar numerator

    N_u(k)=fhat_u(-k)^T P(k) fhat_u(k),                    (6.1)

where k is taken in the local complex neighborhood of k_*, with torus
periodicity understood. On real k this is the usual nonnegative band
overlap |phi(k)^* fhat_u(k)|^2. At the TRIM,

    N_u(k_*)=(w^T u)^2.                                  (6.2)

For the selected branch u_xi and any family of complex points
k(xi)->k_*, continuity gives

    N_(u_xi)(k(xi)) -> ||P_lambda w||^2 >0.                (6.3)

In particular it is nonzero for all sufficiently small xi. This conclusion
does not require treating a complex eigenvector's conjugate transpose as
holomorphic: (6.1) uses the analytic Riesz projection and the paired
Laurent polynomials, which is the appropriate analytic continuation.

There is an effective finite-parameter version. The fixed support and
local analytic projection bounds give a uniform constant C_N with

    |N_u(k_*+q)-N_u(k_*)|<=C_N |q|

for real unit u and sufficiently small complex q. If a subsequent band
analysis locates all its relevant critical points in |q|<=R sqrt(xi),
it is enough to verify

    |w^T u_xi|^2 > 2 C_N R sqrt(xi).                       (6.4)

Then each such numerator has magnitude at least |w^T u_xi|^2/2.
Condition (6.4) eventually holds by (4.3). The locations, dominance,
Hessians, residue denominators, and contour deformation of those critical
points are separate obligations. This lemma proves their numerator cannot
vanish once those points are known to approach this edge; it does not
assume their existence or prove a Green-function asymptotic by continuity.

For purely imaginary displacements q=i beta with beta real, the conclusion
is stronger: the numerator is **positive real**. In the anchor gauge,
H_0(k_*+i beta) is a real matrix because every Laurent phase is a real
Bloch sign times a positive exponential. Its isolated simple eigenvalue
near E_* and the corresponding Riesz projection remain real: complex
conjugation fixes the matrix and the unique rank-one spectral cluster.
The finite Fourier source polynomials at k_*+i beta and its negative are
also real. Thus N_u(k_*+i beta) is real, and (6.4) gives

    N_(u_xi)(k_*+i beta)>=|w^T u_xi|^2/2>0

simultaneously for every real beta with |beta|<=R sqrt(xi). This is uniform
over directions, rather than a separate pointwise continuity assertion.

## 7. Effective dyadic background selection

The physical background must be represented by short rational coefficients.
E_* need not be dyadic. Therefore do **not** set xi to a dyadic and assume
E_*-xi is an allowed finite datum. Instead choose a dyadic number z with

    0<z<E_*,       xi=E_*-z>0,

and set

    epsilon_b' = epsilon_b+z/t.

For the fixed dyadic t=1/64, this background is dyadic. More
generally, fixed rational t also gives fixed rational coefficients. The
algebraic fiber eigenvalue E_* at the TRIM can be isolated with exact
finite-dimensional polynomial arithmetic. Thus a sequence of dyadic
z approaching E_* from below is effectively computable, with certified
positive lower and upper bounds on xi. Require xi<g_-/2 and any other
known fixed smallness limits from the band-edge data.

The proof of Lemma 4.1 uses the abstract eigenspaces of S_0. Their exact
multiplicities need not be decidable from approximate entries, and the
algorithm does **not** try to decide them. Instead dovetail over the
dyadic shifts and finite-precision certificates for S_xi itself:

1. Use a known positive rational lower bound on the gap of H_xi and a
   known rational norm bound to evaluate finite-propagation inverse
   polynomials with rigorous norm error tending to zero.
2. Compress to T_l=Q P_l(H_xi)Q^T. The matrix W T_l is rational and
   similar to W^(1/2)T_lW^(1/2). Exact polynomial root isolation or
   rational inertia tests can isolate a simple eigenvalue of S_xi above
   T+1, with a certified complementary spectral gap. To certify simplicity,
   count algebraic multiplicities; disjoint intervals for distinct roots
   alone are insufficient.
3. Certify a normalized approximate eigenvector by its residual and the
   complementary gap. Spectral expansion gives an explicit norm distance
   to the unique real eigenvector. The vector w is computable from the
   simple algebraic fiber eigenpair, so certify |w^T u_xi|>0.
4. When needed, require the quantitative inequality (6.4) using the
   supplied critical-point radius bound R and the local numerator bound.

For the branch (4.3), these are strict inequalities for every sufficiently
small xi. Arbitrarily accurate local inverse and eigenpair certificates
therefore eventually pass. Dovetailing terminates. It returns fixed
dyadic background data, fixed rational spectral separation and overlap
bounds, and a fixed admissible scalar tuning interval. No equality test
on the limiting matrix S_0 is hidden in this argument.

The fixed search can be extraordinarily large. It is an effectively
terminating constant precomputation, independent of the sparse input size.
It has not been executed here. Once its constants are fixed, later
inverse-polynomial calibrations use the usual local inverse polynomial
and isolated-mode refinement in polylogarithmic precision. Enlarging the
period to contain the defect support is allowed without changing the
material; it folds the same unique edge into the larger Brillouin zone.
Its quadratic anisotropy is unchanged up to scalar rescaling of momentum.

## 8. Conclusions and their application to the certified background

Given the band-edge data in Section 1, the argument proves:

* an admissible dyadic periodic background with a fixed complete gap;
* a finite all-cell scalar defect with a simple positive compressed mode;
* a two-sided scalar tuning interval with fixed upper material headroom;
* a unique localized physical mode;
* nonzero edge Bloch overlap and nonzero analytic numerators at all
  sufficiently nearby complex critical points;
* effective selection and finite exact acceptance without a generic
  material perturbation or an exact multiplicity decision at the edge.

The separate finite certificates now establish the actual edge and its
geometry for the inversion-FCC material. The following section supplies
the elementary integer-lattice approximation used in the rate comparison;
`../main/discrete_edge_green_lemma.md` supplies the global complex
resolvent domain, full-block upper bound, directional asymptotic, and
uniform remainder. `../main/composition_audit.md` supplies the finite-PEC
composition. These are explicit separate dependencies, not additional
conclusions of the present lemma alone.

The fixed cube, operating shift, and isolated mode are selected by the
terminating effective searches proved above. No numerical execution of
that enormous fixed search is asserted. Its input-size independence and
the subsequent precision-refinement cost are included in the master
theorem's uniform algorithm.

## 9. Optional integer change of the defect translation lattice

This elementary lemma may remove a separate near-isotropy requirement in
the subsequent H3 proof. It concerns positions of translated defects; it
does not rotate the Yee stencil, change scalar material values, or apply a
PML stretch.

Let A be the positive-definite quadratic form from (1.2), with
lambda_min(A)>=a_0>0. Choose an integer K_wh>=60/sqrt(a_0), and choose an
integer matrix T whose entries differ from those of K_wh A^(1/2) by at
most one. This can be done by certified approximation and rounding,
without deciding an exact rounding tie. The error has Frobenius norm at
most three. Therefore

    T=K_wh A^(1/2)(I+F),       ||F||<=1/20.

In particular T is nonsingular. For translations by Tn, the relevant
quadratic form in dual logical coordinates is

    A_eff=T^(-1) A T^(-T)
         =K_wh^(-2)(I+F)^(-1)(I+F)^(-T),
    lambda_max(A_eff)/lambda_min(A_eff)
       <=(21/19)^2=441/361<4/3.                           (9.1)

Consider only the leading quadratic dispersion. A cube of imaginary
logical shifts with half-width eta is inside its resolvent ellipsoid
provided 3 lambda_max(A_eff) eta^2<xi. Hence the available logical-l1
upper decay rate approaches

    eta_up=sqrt(xi)/sqrt(3 lambda_max(A_eff)).

For an intended translation T e_j, the directional support rate is

    I_j=sqrt(xi) sqrt(e_j^T A_eff^(-1)e_j)
        <=sqrt(xi)/sqrt(lambda_min(A_eff)).

Equation (9.1) gives the strict inequality

    2 eta_up > max_j I_j.                                (9.2)

Thus the small-xi tube and directional asymptotic separately proved in
`../main/discrete_edge_green_lemma.md`, with
errors tending to zero relative to these quadratic rates can preserve the
strict rate margin needed for r^2<a. This is a statement about those
quadratic rates; the full contour theorem is the named separate dependency.

T need not be unimodular. Restricting centers to its sublattice introduces
no physical obstruction: the original background is invariant under every
integer period translation, hence under Tn. The local calibration still
uses fixed-support defects. For sufficiently large separation d the
translates dTn are disjoint because T is nonsingular. Symmetry of the real
resolvent gives equal couplings in opposite directions, so mediators have
matching two-sided incident couplings along each T e_j.

The constructive R5 proof in `r5_constructive_proof.md` outputs a box with
all three side lengths O(sqrt(S)). A fixed integer linear transform T,
followed by a common separation factor d and padding, has a containing
axis-aligned physical box of volume O_T(S^(3/2)d^3). Therefore the skew
translation lattice does not change the required asymptotic volume in
this particular logical reduction. For an arbitrary highly elongated
logical box, a separate volume argument would be needed; that case is
not silently assumed here.
