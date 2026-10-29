# Audited conditional physical composition

## Scope

This is an analytic implication from the stated bulk, isolated-defect, and
coupling hypotheses to the requested physical reduction. It does **not**
by itself prove the coupling hypothesis. That hypothesis is now supplied
for the certified inversion-FCC background by `discrete_edge_green_lemma.md`
and `../logical/edge_mode_route.md`, with the accepted finite premises
assembled in the master theorem. The constructive
logical theorem in `../logical/r5_constructive_proof.md` replaces the old
unproved R5 black box. The existing 392-cell defect is not assumed certified.

Use fixed rational background data, period P, frequency omega=1/8, t=1/64,
and an isolated scalar-cell defect with weights W, normalized mode u,
Birman–Schwinger eigenvalue mu, and complementary separation gamma_d.
The background gap is g0, its absolute row/column bound is J, and its
stencil radius is r_H. Suppose its full interaction blocks obey

    ||G(n)|| <= C0 r^|n|_1,
    |u^T G(d e_j)u| >= c a^d,
    0<r,a<1,  r^2<a,

with all constants fixed and effectively computable. Rational upper/lower
bounds may replace nonrational constants. Sufficiently small two-sided
scalar tuning and positive uniform detuning must leave material headroom.
The bounded-window, independently spaced-axis variant in
`../defects/bounded_window_coupling.md` also suffices, with its explicitly
stated asymptotic premises. The direct simple-edge variant is the one
used in the completed analytic construction; the bounded-window variant
is not needed for that application.

## 1. A precise finite PEC convention

Let scalar cells be indexed by
0<=i<Nx, 0<=j<Ny, 0<=k<Nz. Retain the electric x-edges with

    0<=i<Nx, 1<=j<Ny, 1<=k<Nz,

and cyclically retain y- and z-edges. These are the edges not contained
in the boundary of the cubical complex. Tangential electric edges on the
boundary are fixed to zero. Keep every square-face curl row, including
zero boundary-face rows if convenient. This is the relative-cochain PEC
incidence convention.

Every retained electric edge has four incident scalar cells, all inside
the rectangular cell domain, and four incident faces. Hence its material
average uses exactly four values. Every curl row has at most four entries
of magnitude one. Thus C^T C has diagonal four and absolute off-diagonal
row sum at most twelve. For epsilon in [1,25],

    0<4-t epsilon_edge<4,
    ||C^T C-tD_epsilon||_1,inf <=16.

The operator is real symmetric. A uniform scalar-cell increment u/t adds
exactly u I to tD, including edges adjacent to the PEC boundary. No
fractional boundary weights are silently discarded. The finite incidence
stencil agrees with the infinite one away from the boundary.

Use any fixed collar width, or no collar. With a collar, assign material
by coordinatewise clamping from the physical region, and use s=1. All
defect cells and source stencils remain inside the physical region.
The following argument does not use absorption or a finite-box bulk gap.

## 2. Logical layout and signed mediator algebra

Let Gamma be the logical matrix of the constructive theorem, with
||Gamma||<=7, degree at most three, positive unit edges, and known
Kbar>=max(1,||Gamma^-1||). Let g be its source and 0<epsilon<=1/2 its
requested relative residual. For d sufficiently large define

    zeta=r^d,   alpha=(c/4)a^d.

For zeta<=1/2 the lattice sums satisfy

    sum_(n!=0) zeta^|n|_1 <=64 zeta,
    sum_(|n|_1>=2) zeta^|n|_1 <=256 zeta^2.

They follow by expanding ((1+zeta)/(1-zeta))^3. Their respective
numerators are 6zeta+2zeta^3 and
18zeta^2-16zeta^3+6zeta^4; the denominator is (1-zeta)^3.
A matrix of block norms and its row sums therefore bound the operator
norms, without a factor equal to the number of defects.

Double the logical lattice. Place terminal defects at doubled logical
sites and one mediator defect at the midpoint of each actual logical
edge. Scale by Pd. Only terminal–mediator incidences are nearest occupied
neighbors in these lattice coordinates. Approximate
beta_j=-u^T G(d e_j)u with absolute error <=zeta^2. Requiring zeta^2<=alpha
gives |beta_j|>=3alpha and |beta_j|<=(C0+1)zeta.

Set the effective target diagonals to

    T_ii=alpha(Gamma_ii-degree(i)),
    T_ee=-beta_j^2/alpha,

and both incidences of a j-mediator to beta_j. Translation invariance and
real symmetry ensure the two incidence couplings agree, including sign.
The mediator Schur complement is exactly alpha Gamma. If E_m and D_m
are its coupling and diagonal blocks,

    ||D_m^-1||<=1/alpha,
    ||E_m D_m^-1||<=sqrt(6),
    ||T^-1||<=16 Kbar/alpha,
    ||Gamma z_T-g|| <=(4/alpha)||Tz-alpha(g,0)||.

The triangular factorization proves these bounds. Required on-site
shifts have magnitude at most

    max(7alpha,(C0+1)^2 zeta^2/alpha).

Both terms tend to zero because zeta^2/alpha=(4/c)(r^2/a)^d.

## 3. Finite boundaries and a random uniform shift

Surround all defects by a physical buffer b, measured from the full
source stencil, and then the fixed collar. Let K0 be the finite background
matrix and n its dimension. Choose dyadic tau within fixed factors of
zeta^2, sufficiently small that

    tau<=g0/4,  tau<=g0^2 zeta^2/16,

and tau/t fits the available scalar material headroom. Let J_grid be
the least power of two at least 16(m+n)^2. Independently sample

    u_shift=(j+1/2)tau/J_grid, 0<=j<J_grid,
    K=K0-u_shift I,    L=16(m+n)^2/tau.

For each real eigenvalue of K0, the interval of radius 1/L contains at
most 2J_grid/(L tau)+1 grid points. Therefore

    Pr(||K^-1||>L) <=2n/(L tau)+n/J_grid
                    <=3n/[16(m+n)^2] <=3/(64m)<1/m.

Singular draws are included in this bad event. This argument applies to
the real symmetric unstretched operator, not to arbitrary complex PMLs.

For |u_shift|<=g0/4 define R_u=(H-u_shift I)^-1 and

    mu_b=(1/r_H)log(1+g0/(4J)).

Conjugate by bounded clipped exponential distance weights. The matrix
change has row/column sums <=g0/4; a Neumann series gives the norm bound
2/g0 on the weighted inverse. Removing weights gives

    ||P_X R_u P_Y^T|| <=(2/g0)exp(-mu_b dist_1(X,Y)).

Let P restrict the infinite lattice to the box and T_b=K0 P-PH.
Its nonzero input coordinates lie in a fixed-width boundary/collar strip;
||T_b||<=2J after a fixed enlargement if needed. Taking the buffer from
this strip absorbs all stencil-width constants. Direct multiplication
gives

    K^-1 Q^T-P R_u Q_infty^T=-K^-1 T_b R_u Q_infty^T.

Together with R_u-R=u_shift R_u R, on the good event this proves

    ||QK^-1Q^T-Q_infty RQ_infty^T||
      <=2tau/g0^2+(4JL/g0)exp(-mu_b b).

Q selects the **entire union** of defect coordinates. The distance-weight
bound is an operator estimate for sets, so the number of defects does
not multiply its right side. Choose b to make this bound <=zeta^2.
The box dimension is at most a fixed polynomial in m,d,b. Successive
doubling therefore terminates at b=O(d+log m); equivalently the exponential
in b eventually dominates the fixed power of b in L. The dimensions are
computed arithmetically before materializing the successful box.

## 4. Scalar-cell tuning and elimination of nonresonant modes

Choose the common increment v_i/t for each defect's scalar cells so that

    |v_i^-1-(mu+T_ii)|<=zeta^2.

Round scalar cells, not electric-edge coefficients. The scalar tuning
interval, the small on-site shifts, and the separately reserved uniform
headroom guarantee admissibility for large d. Write

    V=diag(v_i W),    A=K-Q^T VQ,
    M=W_all^(1/2)(V^-1-QK^-1Q^T)W_all^(1/2).

Let U place u in each block and complete it by orthonormal Z. In this
basis write M=[B E; E^T D_c]. At infinite separation the complementary
block consists of mu I-S0 on u-perp, with smallest singular value at
least gamma_d. It may be indefinite. The inverse perturbation lemma,
not positive definiteness, gives for sufficiently large d

    ||D_c^-1||<=D_*=2/gamma_d,
    ||E||<=64C0 zeta+zeta^2,
    1+||E||D_*<=2.

On-site scalar shifts have zero mixed u/u-perp block. The bright-block
error comprises one on-site rounding unit, three incidence row-sum units,
one finite-background unit, and the non-neighbor tail. Thus

    S_b=B-E D_c^-1 E^T=T+Delta,
    ||Delta||<=C_D zeta^2,
    C_D=256C0+5+D_*(64C0+1)^2.

Require

    C_D zeta^2<=alpha epsilon/(4096Kbar).

All requirements on d are fixed geometric inequalities, so
d=O(1+log Kbar+log(1/epsilon)). The inverse perturbation lemma yields
||S_b^-1||<=32Kbar/alpha. A second triangular elimination gives the
terminal response alpha Gamma+Delta_eff with

    ||Delta_eff||<=12||Delta||+288||Delta||^2/alpha
                 <=13||Delta||.

Indeed the unperturbed mediator-elimination triangular matrix has norm
less than sqrt(12), its transformed lower-right perturbation is still
Delta_II, and ||Delta||/alpha<=1/8192. This is a response estimate, not
an assertion that the raw physical interaction matrix is scalar.

## 5. Full conditioning and local source/readout

Set

    Q_M=4(32Kbar/alpha+D_*),
    Q_A=L+L^2 Q_M,    c_W=1/sqrt(w_min).

Block factorization and direct Woodbury multiplication give

    ||M^-1||<=Q_M,
    A^-1=K^-1+K^-1Q^TW_all^(1/2)M^-1W_all^(1/2)QK^-1,
    ||A^-1||<=Q_A,    kappa(A)<=JQ_A.

Thus the full Maxwell condition number is controlled; a good terminal
Schur condition number alone would not suffice.

For g_T=(g,0), define the ideal source and readout

    f_*=alpha KQ^TW_all^(-1/2)Ug_T,
    z=U^TW_all^(-1/2)VQy.

The source requires one finite stencil application to defect-supported
vectors, so its complete support is in the physical region. Its norm is
at most alpha J c_W||g||. No background solve appears in either map.
For r=Ay-f_* the exact residual identity is

    S_b z=alpha g_T+
       (U^T-E D_c^-1 Z^T)W_all^(1/2)QK^-1 r.

To verify it, first put w=W_all^(-1/2)VQy. Multiplication gives
Mw=W_all^(1/2)QK^-1(f_*+r)=alpha Ug_T+
W_all^(1/2)QK^-1r. Orthogonal projection and elimination of the second
block give the displayed equation. Its residual operator has norm <=2L.

Choose physical relative tolerance

    delta_phys=epsilon/(8192 J c_W L),

and round the source to f_hat with
||f_hat-f_*||<=alpha epsilon||g||/(8192L).
Every y with ||Ay-f_hat||<=delta_phys||f_hat|| then satisfies

    ||z||<=33Kbar||g||,
    ||Tz-alpha g_T||<alpha epsilon||g||/64,
    ||Gamma z_T-g||<epsilon||g||/16.

These inequalities follow by substitution in the exact identity and
the preceding inverse bounds. They hold for every physical residual
solution on the good event, irrespective of how that solution is found.
If the solver supplies a complex vector, take its real part before
readout: A and f_hat are real, and
||A Re(y)-f_hat||<=||Ay-f_hat||. Thus the same guarantee supplies a real
logical solution and a real decoded solution of the original system.

## 6. Finite calibration, coefficients, and decoding

Indefiniteness does not prevent local inverse calibration. For l>=0,

    P_l(H)=(H/J^2)sum_(j=0)^l(I-H^2/J^2)^j,
    ||H^-1-P_l(H)||<=g0^-1(1-g0^2/J^2)^(l+1).

Its propagation radius is at most (2l+1)r_H. With fixed rational
background coefficients, a column to inverse-polynomial accuracy takes
O(log m) stencil iterations on O(log^3 m) coordinates, with polynomial
in log m bit cost. All constants, including very large background
period and support constants, must first be fixed independently of m.

The finite-dimensional simple eigendata can be approximated at the
same precision by certified inertia/root isolation, or by the squared
spectral filter centered inside its isolating interval. One must use a
filter isolating the actual eigenvalue, not an unjustified largest-mode
iteration in an indefinite matrix.

Let q=W^(1/2)u and v_max be a fixed bound for |v_i|. It suffices to
compute q_hat with

    ||q_hat-q||<=min(w_min epsilon/(32768JL),
                    epsilon/(1024 v_max alpha J c_W Q_A)).

The source uses W^-1 q, so its coefficient error is bounded by the first
term. The readout error follows from
||y||<=3alpha J c_W Q_A||g|| and the second term. Allow a further
epsilon||g||/128 for readout arithmetic, including rounding accessed y
coordinates. Since ||Gamma||<=7, the final logical residual remains
less than epsilon||g||/2. Polynomial bounds on ||y|| and the number of
read coordinates give an explicit O(log m)-bit absolute rounding grid.
The decoder reads only the precision it needs and never solves Gamma
or the original system.

Normalize ||g||_infinity=1 unless g=0. Then ||g|| lies between one and
the square root of its dimension, and all source norms and tolerances
are polynomially bounded. Dyadic material and source output uses
O_{k,C}(log m) bits. Intermediate local exact arithmetic may use a fixed
power of log m bits without changing soft-O construction time.

## 7. Size and an explicit exponent budget

The logical proof supplies a balanced box with side O(sqrt(S)),
S=O(m log m). Thus doubling, scaling by Pd, physical buffering, and
fixed collars give

    N=O(S^(3/2)(Pd+b+O(1))^3)=O_tilde(m^(3/2)).

The same bound holds after any fixed integer change of lattice basis
used in the Hessian-whitening argument: balanced boxes, unlike
arbitrarily elongated boxes, expand by only a fixed volume factor.
Every empty physical cell and every electric unknown is counted.
Writing the material/source arrays costs O_tilde(N); per-defect local
calibration costs only polylog m with fixed background constants.

For the square problem write K=ceil(k), C0_in=ceil(C). The logical
inverse bound is O_tilde(m^(K+6)), and its residual amplification is
O_tilde(m^(5/2)). Hence one may use fixed safe exponents beta=K+8 and
chi=C0_in+4, absorbing their fixed constants, with
Kbar<=constant*m^beta and epsilon^-1<=constant*m^chi.

Let rho=r^2/a<1. Selecting

    d>=log[(16384 C_D/c)Kbar/epsilon]/log(1/rho)

and the fixed ancillary lower bounds suffices. Rational geometric
inequalities permit a certified integer choice without assuming exact
real logarithms. For suitable fixed D1>(beta+chi)/log(1/rho),
d<=D0+D1 log m. Set

    p>D1 log(1/r),    q>D1 log(1/a).

Then zeta^-1=O(m^p), alpha^-1=O(m^q), and

    L=O_tilde(m^(3+2p)),
    kappa(A)=O_tilde(m^(6+4p+q+beta)),
    delta_phys^-1=O_tilde(m^(3+2p+chi)).

To obtain the literal promises kappa(A)<=m^q and delta_phys>=m^(-s),
absorb logarithms and constants by an effectively computed exponent
increment, not automatically by one. For example, if a proved bound is
Q<=K_const*m^a*(log(2+m))^b for m>=2, choose an integer B_log>=b.
Since log(2+m)<=m, it suffices to take

    q_int=ceil(a+B_log)+ceil(log_2(max(1,K_const))).

The last integer can be selected by rational doubling. Apply this
separately to the condition and inverse-tolerance bounds. The finitely
many base cases, including m=1, use the explicitly counted exact encoding
and one-edge PEC instance described in the master theorem. All exponent
increments depend only on the fixed input promises and effectively
selected background data. The rectangular transfer has its separate
explicitly padded square promises and uses the same construction with
those fixed exponents.

## 8. Scope of the conditional consequence

Composing this implication with the proved rectangular transfer gives
time O_tilde(m^(3/2)+m^(3theta/2)) from a Maxwell solver of exponent theta.
Only for gamma>3/2 and theta<2gamma/3 does that contradict the matching
randomized SLTH. Runtime caps and verification of the original saddle
residual control bad random draws. The conclusion would concern uniform
worst-case guarantees, not all subclasses and not a cost N poly(kappa).

This document remains a general implication with explicit hypotheses.
The actual hypotheses are now discharged by the finite edge certificates
and analytic defect/coupling lemmas named above. The master proof gives
the resulting uniform reduction, retains the fixed preprocessing as
analytically terminating rather than numerically executed, and records
the completed final clean replay. Its SLTH consequence requires the separately
stated matching randomized hypothesis.
