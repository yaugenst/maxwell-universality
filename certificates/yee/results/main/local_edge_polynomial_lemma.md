# Certifying a whole L-neighborhood by a polynomial spectral test

## Scope

This analytic lemma reduces local band minimality on the entire Euclidean
radius-1/20 ball to a small number of finite matrix inequalities at its
center, plus a uniform inertia bound. The hypotheses below must be
established by the separate exact local spectral certificates. The scalar
arithmetic is independently checked in `verify_local_edge_scalar.py`.
The lemma is not a claim that floating-point Hessians or sampled points
certify a neighborhood.

## 1. Finite hypotheses and conventions

Let A(q) be the electric Bloch matrix of the inversion-symmetric candidate
near one of its L points, in the centered Yee gauge. The coordinates q are
Cartesian reciprocal coordinates in the convention exp(2 pi i q/20).
Assume the following certified facts.

* For every |q|<=1/20, A(q) has exactly two eigenvalues in (0,b), with
  b=7/256, and all other eigenvalues are outside [0,b]. (An at-most-two
  assertion, together with the positivity argument below, also suffices.)
* At q=0, these two eigenvalues are E and E+delta, where
  0.00956<=E<=0.00957 and 0<delta<=2^(-20).
* U is an exact orthonormal basis of their two-dimensional invariant
  subspace, with (A(0)-E)U=U Delta, where Delta is positive semidefinite
  with eigenvalues 0 and delta. It may be made diag(0,delta) by an
  internal unitary change of basis, but this is not necessary. The two
  columns have the
  same eigenvalue sigma in {1,-1} under an exact unitary inversion I.
  In the centered gauge I A(q) I=A(-q).
* Write A_j(q) for the homogeneous term of degree j in A(q). The
  opposite-inversion-parity restriction of A(0)-E is invertible. Define
  Y(q) in that subspace by

      (A(0)-E)Y(q)=A_1(q)U.

  This is a linear function of q. Its certified bound is ||Y(q)||<=3|q|.
* Define

      K2(q)=U* A_2(q)U-U* A_1(q)Y(q),
      R2(q)=A_2(q)U-A_1(q)Y(q).

  For every q and every two-vector x, certify

      (1/50)|q|^2 I <= K2(q) <= |q|^2 I,
      ||R2(q)x||^2 <= (18/5)|q|^2 x* K2(q)x.            (1)

These are finite matrix inequalities. For instance, write K2(q) as the
compression of a 6-by-6 Hermitian coefficient matrix to q tensor x.
A positive-definite lower bound for that coefficient matrix implies the
first inequality. For the second, write R2 as a sum q_i Z_i(q tensor x),
apply Cauchy-Schwarz in i, and dominate the finite Gram matrix sum Z_i*Z_i
by (18/5) times the K2 coefficient matrix. This sufficient Gram test is
stronger than checking a finite mesh of directions and covers every real q.

U and Y in this statement are the exact objects. Rational dyadic witness
vectors may certify their enclosures by residual and gap bounds, but
must not replace the exact identity (A(0)-E)U=U Delta at q=0. A small
uncontrolled negative constant error would invalidate every-radius
minimality arbitrarily close to zero.

## 2. Explicit Taylor bounds from the Yee sine symbol

In the centered electric/face gauge, the free curl is a cross-product
matrix whose symbol components are 2 sin(pi(G_j+q_j)/20), up to fixed
unitary factors. Scalar material is diagonal and unchanged by the gauge,
so all positive-degree Taylor terms of A come from C(q)*C(q).
For theta=pi/20<11/70 and r=|q|, its homogeneous terms obey

    ||C_0||<=2 sqrt(3)<7/2,
    ||C_j(q)||<=2 theta^j r^j/j!,    j>=1.

For the second inequality use
(sum |q_l|^(2j))^(1/2)<=|q|^j and the componentwise sine derivative
bound. The norm of a real cross-product symbol is its Euclidean norm.
Multiplying the curl series gives

    ||A_j(q)||<=a_j r^j,
    a_j=[4*2^j+6] theta^j/j!,    j>=1.                   (2)

The identity uses 2||C_0|| times the jth curl term and the j-1 interior
convolutions. It is valid uniformly over all Fourier characters and
therefore for the entire finite Bloch matrix. The material and E affect
only the zeroth term.

Let F(q)=U-Y(q), and R(q)=(A(q)-E)F(q). Then R_1=0 exactly. Inversion
makes F(q)*(A(q)-E)F(q) even. The even and odd components of R occupy
orthogonal parity subspaces. Thus, writing r=|q|,

    F*(A-E)F=Delta+K2+K_rem,
    R_even=U Delta+R2+R_even,rem,
    R_odd=R3+R5+...,

with the uniform estimates for 0<=r<=1/20

    ||K_rem||<=(13/5)r^4,
    ||R_even,rem||<=(2/25)r^4,
    ||R_odd||<=(17/20)r^3.                              (3)

To verify (3), the first leading coefficients are bounded respectively by

    a4+6a3+9a2,    a4+3a3,    a3+3a2.

For each relevant coefficient sequence, the ratio of the next even-degree
term at r=1/20 to the current one is at most

    (2*(11/70)*(1/20))^2/12 < 1/40000.

Indeed a_(j+2)/a_j is at most 4 theta^2/[(j+1)(j+2)], and the smallest
denominator in the shifted sequences is 12. Summing the geometric
majorant multiplies each displayed leading coefficient by at most
1/(1-1/40000). Exact rational comparison gives (3).

## 3. Positivity of the polynomial spectral test

Use the degree-two spectral polynomial

    g_E(A)=(A-E)(b-A)=(b-E)(A-E)-(A-E)^2.               (4)

Since A(q) is Hermitian for real q,

    F* g_E(A)F=(b-E)F*(A-E)F-R*R.                      (5)

The constant term is Delta[(b-E)I-Delta], positive semidefinite. The
term U*R2 is exactly K2. Odd cross terms vanish by the orthogonal
parity decomposition, rather than being bounded by their norms.

Put k_min=1/50, k_max=1, c2=18/5, k4=13/5, c3=17/20, c4=2/25.
For every x, the inequalities (1)--(3) imply

    x* F* g_E(A)F x
      >= x*Delta[(b-E)I-Delta]x + L(r) x*K2(q)x,        (6)

where a valid lower bound is

    L(r)=(b-E)
          -2 delta k_max/k_min
          -c2 r^2 -(b-E)(k4/k_min)r^2
          -(2 delta c4/k_min)r^2
          -[2 sqrt(c2)c4/sqrt(k_min)+c3^2/k_min]r^4
          -(c4^2/k_min)r^6.                            (7)

Here are the bounds on all terms in (5), so none is silently discarded.
The Delta/K2 anticommutator is bounded in absolute value by
2 delta k_max r^2 ||x||^2, hence by
(2 delta k_max/k_min)x*K2 x. This argument does not falsely assume that
Delta and K2 commute. The R2 norm square is bounded by c2 r^2 x*K2 x.
The K_rem term costs (b-E)(k4/k_min)r^2 x*K2 x.
The U Delta/R_even,rem cross term costs
(2 delta c4/k_min)r^2 x*K2 x. Cauchy-Schwarz and (1) bound the
R2/R_even,rem cross term by
2 sqrt(c2)c4 r^4/sqrt(k_min) times x*K2 x.
The remaining even norm square costs (c4^2/k_min)r^6 times x*K2 x,
and the entire odd norm square costs (c3^2/k_min)r^4 times x*K2 x.
These enumerate the full square R*R.

All losses increase with r and delta. Use the lower bound on b-E for
its positive occurrence and the upper bound for its negative occurrence.
The exact scalar calculation uses

    r=1/20, delta=2^(-20),
    b-E in [7/256-957/100000, 7/256-239/25000],
    sqrt(c2/k_min)=sqrt(180)<27/2.

It gives L(r)>1/400 throughout the ball. In particular,

    F(q)*g_E(A(q))F(q) >= (1/20000)|q|^2 I              (8)

for q!=0. The separate exact scalar checker recomputes these rational
inequalities; it does not accept precomputed decimal margins.

## 4. From trial-space positivity to the two actual bands

Parity also gives U*Y(q)=0, and therefore

    I <= F*F=I+Y*Y <= (1+9r^2)I <= (409/400)I.          (9)

Thus F has rank two. By the Hermitian min-max principle, the second
largest eigenvalue of g_E(A(q)) is at least
|q|^2/[20000(409/400)]=|q|^2/20450.

The scalar polynomial g_E(lambda) is positive exactly for E<lambda<b.
All eigenvalues of A outside [0,b] give nonpositive values. The uniform
inertia hypothesis therefore implies both of its two bands in (0,b)
lie in (E,b), and each satisfies

    (lambda-E)(b-lambda) >= |q|^2/20450.

Since b-lambda<b and b=7/256,

    lambda(q)-E > |q|^2/600,       0<|q|<=1/20.         (10)

At zero, the two values are E and E+delta with delta>0. Consequently E
is the unique minimum in this ball. The lower branch is analytic and
simple near zero; by inversion its first derivative vanishes. Comparing
its Taylor expansion with (10) proves its Hessian is at least (1/300)I.
This already gives a certified Morse minimum; sharper certified Hessian
entries may be used later for a more efficient whitening matrix.

## 5. What remains outside this lemma

Apply the finite hypotheses and this argument separately at all four
inequivalent FCC L points. Compare their isolated exact E intervals to
choose the unique lowest one. A separate certificate must exclude lower
values on the complement of the four balls over the full Bloch torus.
Symmetry of the unperturbed comparator may be used for that global
certificate, but symmetry broken by the actual perturbation cannot be
used to identify the four perturbed minima. The global cover and the
finite matrix hypotheses are not inferred from this scalar lemma.
