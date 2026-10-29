# Independent assembly audit for the global Yee band edge

## Status and purpose

This note audits the mathematical implication of the finite certificate set.
It does not replace the fresh full matrix checks. The current master ledger
records whether those checks have passed. In particular, a geometric cover
and proposed witnesses alone do not discharge the premise below.

Let H0(kappa) be the original period-20 diamond electric Bloch matrix, let
Hp(kappa) be the canonical inversion-symmetric scalar perturbation, and put

    t = 1/64,
    s = 157/16384,
    sigma = 1/2^24,
    rho = 1023/2^26.

There are 6000 electric coordinates in the FCC primitive fiber and 2000
scalar-cell representatives. The two magnetic negative directions in the
matrix certificate correspond to 2002 negative electric directions after
including the gradient sector. At Gamma the free curl kernel has dimension
2002, so the analytic Gamma argument has the same electric count.

## 1. What a successful shifted box proves

The shifted original material is Dprime = D0 + 64s I. It satisfies
I <= Dprime < 13 I. The magnetic exact interval certificate excludes
positive generalized curl eigenvalues from [t-sigma,t+sigma] and gives
exactly two transverse eigenvalues below this interval. The artificial
positive gradient block used by the verifier is removed in this count.
The nonzero eigenvalues of C Dprime^(-1) C* and
Dprime^(-1/2) C* C Dprime^(-1/2) coincide with multiplicities.
Consequently the generalized electric matrix has 2002 eigenvalues below
-sigma and all remaining eigenvalues above sigma after subtracting t I.

Congruence gives

    H0-sI = Dprime^(1/2)
              (Dprime^(-1/2) C* C Dprime^(-1/2)-tI)
            Dprime^(1/2).

Its inverse norm is at most 1/sigma because Dprime >= I, and Sylvester
inertia is unchanged by this congruence. It follows that H0-sI has exactly
2002 negative eigenvalues and its first positive eigenvalue is at least
sigma. This uses both the inverse bound and the inertia: invertibility
alone would not identify the relevant band. The corresponding original
electric rank-2003 eigenvalue is therefore at least s+sigma.

The analytic Gamma comparison independently gives this same conclusion
on the entire cube |kappa_j| <= 1/8. Thus it also handles the singular
magnetic gradient-projector point without taking a numerical limit.

## 2. Transfer to the actual scalar material

Every added cell value is between zero and 1023/2^20. Four-cell averaging
is positive and contractive in the maximum norm, so

    H0-rho I <= Hp <= H0.

The original H1 certificate gives no spectrum in (-1/4096,1/4096).
Since rho < 1/4096, this perturbation preserves the number 2002 of
negative eigenvalues throughout the Bloch torus. In particular, the
first positive band is the same ordered eigenvalue in both matrices.
Hermitian eigenvalue monotonicity gives, on every shifted certified box,

    lambda_positive(Hp) >= s+sigma-rho = 642053/2^26.

The point residual and inertia certificates give
E_c = lambda_low(Hp(L++-)) < 23913/2500000. Exact subtraction yields

    642053/2^26 - 23913/2500000 > 1/500000.

The comparison applies separately at every momentum. It does not assign
the broken cubic symmetries of H0 to Hp.

## 3. Complete domain and local neighborhoods

The primitive reciprocal lattice consists of integer triples with all
coordinates of the same parity. Its Voronoi zone is

    |kappa_j| <= 1,  sum_j |kappa_j| <= 3/2.

The 48 signed-coordinate permutations reduce the unperturbed comparator
to 0 <= kappa_z <= kappa_y <= kappa_x <= 1 with coordinate sum <= 3/2.
The independent exact polytope/tree checker accounts for all points of
this closed wedge. Every excluded L box is wholly within the Euclidean
radius-1/20 ball, rather than merely having its center in that ball.

The eight signed half-coordinate L points form exactly four classes
modulo the primitive reciprocal lattice; opposite points are equivalent.
Signed permutations preserve Euclidean balls. The excluded comparator
region is therefore contained in the union of the four neighborhoods
for which separate actual-material certificates are available.

At each of these four centers the two low positive modes are isolated,
the lower one is simple, and the polynomial spectral test proves

    lambda_low(Hp(L+q)) - lambda_low(Hp(L)) > |q|^2/600

for every 0 < |q| <= 1/20. All four point values are rigorously ordered,
with L++- lower than every other center by more than 33/10^9.
Together with the global outside-ball comparison, this proves that the
actual operator has exactly one global positive-band minimum modulo
its primitive reciprocal lattice. Its Hessian in kappa coordinates is
at least I/300. No finite sampling argument is used for either region.

## 4. The convention used by the analytic defect and Green lemmas

Use the conventional cubic cell with translations 20e_j and radian
Bloch coordinate k = 2pi kappa. The conventional translation lattice
has index four in the primitive FCC lattice. Fiber decomposition over
the four characters of this finite quotient is a unitary direct sum;
it does not equate the eigenvalues of the four primitive fibers.

The four primitive L classes fold to the same conventional corner
k_* = (pi,pi,pi). Their strict point ordering leaves the lowest folded
eigenvalue simple. The global minimum remains unique on the conventional
torus. The Hessian is

    Q_rad = Q_kappa/(2pi)^2 >= I/(1200 pi^2) > I/12000.

The simple eigenvalue has a computable complex analytic neighborhood:
a contour around its isolated finite-dimensional eigenvalue, followed
by a Neumann estimate for the finite Laurent perturbation, constructs
its analytic projector. Time reversal at the TRIM makes its dispersion
even, so the quadratic Taylor approximation has quartic remainder.
Cauchy estimates give an effective remainder constant and local radius.
The compact separation can also be made explicit from the existing
inequalities. In centered Cartesian coordinates,

    ||C(q)-C(0)|| <= 2(pi/20)|q|,
    ||C(q)||, ||C(0)|| <= 2sqrt(3),
    ||Hp(L+q)-Hp(L)|| < 3|q|.

If delta_cert>0 is a rational lower bound for the lowest L doublet
splitting, then the second band stays at least E_c+delta_cert/2 for
|q|<=delta_cert/6. For any chosen
0<r_inner<=min(1/20,delta_cert/6), the first band outside the inner
ball but inside the local ball lies at least r_inner^2/600 above E_c.
The other L neighborhoods contribute the center-ordering margin
33/10^9, and the remaining torus contributes 1/500000. Their minimum
is an explicit positive bound on the positive-band separation outside
the inner ball. An analytic chart can be chosen still smaller by the
finite Laurent Neumann estimate, with the same formula using its
chosen inner radius. Thus no non-effective compactness constant is
hidden in the defect/Green precomputation.

All bands below E_c are negative. Since E_c > 0.00956 > 1/128, one may
use the rational lower-band separation g_minus = 1/128. The material
satisfies max epsilon <= 12+1023/2^20 and E_c < 0.01, hence

    max epsilon + 64 E_c < 13 = 25-12.

Thus h_mat = 12 is valid for the analytic all-cell defect construction.
These are exactly the premises needed by edge_mode_route.md and
discrete_edge_green_lemma.md, once their named finite certificates have
all been accepted in a clean replay.

## 5. Trusted and unexecuted parts

The finite evidence is ordinary integer/rational and outward-interval
verification with an audited C++ kernel, not proof-assistant verification.
The all-size defect/coupling implication is an analytic proof. It supplies
a terminating fixed search for operating shift, cluster, isolated mode,
and useful decay constants; that very large search is not represented as
an executed computational certificate. The input-size-dependent encoder
uses those fixed computable constants and the separately proved local
calibration procedure.
