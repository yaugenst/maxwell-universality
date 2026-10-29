# An analytic replacement for H2, conditional only on the supplied H1

## Status and exact scope

This is a proof of existence of an effectively computable, admissible,
simple scalar defect for a **slightly modified fixed periodic background**.
It is not a certificate for the supplied 392-air-cell defect. It does not
prove H3, and therefore does not complete the Maxwell reduction. The only
problem-specific premise is the original infinite-background H1 assertion:

\[
H_0=C^*C-D_b/64,\qquad
\operatorname{dist}(0,\operatorname{spec}H_0)\ge g=1/4096,
\quad \|H_0\|\le J=16,
\]

with real period-20 scalar cells in \([1,12]\), on the infinite unstretched
Yee lattice. The exact diamond geometry is not otherwise used. A correct
verification of H1 is still required wherever this lemma is used.

All constants below are fixed independently of the sparse input and requested
accuracy. They are extraordinarily large. The proof gives a terminating
exact search for the final fixed background and the isolated eigenvalue;
it makes no claim that this search has been executed.

## Theorem

Under the premise above there exist an effectively computable integer
period \(P\), dyadic scalar background cells \(\epsilon'_b\), and a finite
cube of scalar defect cells \(\mathcal D\), such that:

1. \(1\le\epsilon'_b\le12+\beta\), where
   \(\beta=g^2/16=2^{-28}\).
2. \(H'=C^*C-D'_b/64\) has gap at least \(g/2\). Its finite stencil is
   unchanged, and a row/column-sum bound can be enlarged by \(g^2/1024\).
3. Every cell of \(\mathcal D\) receives the same scalar increment \(64v\).
   If \(Q\) selects the affected edges and \(W\) records changed
   incident-cell fractions, then \(W_{ee}\in\{1/4,1/2,3/4,1\}\), and
   \(S=W^{1/2}Q(H')^{-1}Q^*W^{1/2}\) has a simple real eigenvalue
   \(\mu>16/3\), separated from all other eigenvalues by a fixed positive,
   effectively computable rational lower bound.
4. For \(v_*=1/\mu\), every
   \(v\in[v_*-g/8,v_*+g/8]\) is admissible. Every background or defect
   cell is at most \(24.5\), leaving material headroom \(1/2\).
   At \(v=v_*\), the infinite physical defect operator has a one-dimensional
   kernel whose nonzero mode is exponentially localized.

Thus H1 and H2 hold simultaneously for this new fixed periodic background,
with the same frequency \(\omega=1/8\), spacing \(h=1\), scalar material
rule, and admissible tuple \((1,25,10,1)\). H3 remains an independent
obligation for the new background and defect.

## 1. A positive spectral point with quantitative room for tuning

Consider the conventional period-20 Bloch fiber at Bloch parameter zero.
The free Yee curl-curl matrix has, for the Fourier wavevector
\((2\pi/20,2\pi/20,0)\), the positive transverse eigenvalue

\[
\lambda_0=8\sin^2(\pi/20).
\]

This follows directly by writing the forward-difference symbol
\(d_j=e^{ik_j}-1\): the curl symbol's squared singular values are
\(0,\sum_j|d_j|^2,\sum_j|d_j|^2\). Staggering only conjugates these
symbols by diagonal unitary phases.

The elementary bounds \(157/50<\pi<22/7\),
\(\sin x\ge x-x^3/6\) for \(0\le x\le1\), and \(\sin x<x\) give

\[
\sin(\pi/20)>157/1000-(11/70)^3/6
 =12871/82320>5/32,
\qquad
\lambda_0<8(11/70)^2=242/1225<1/5.
\]

Consequently \(25/128<\lambda_0<1/5\). Four-cell averaging preserves the
material range, so

\[
\frac1{64}I\preceq D_b/64\preceq\frac3{16}I.
\]

Applying the finite-dimensional min-max principle at any ordered eigenvalue
index occupied by \(\lambda_0\) proves that the same index of the fiber
\(H_0(0)\) has an eigenvalue \(\lambda\) satisfying

\[
\frac1{128}<\lambda<\frac{59}{320}.
\tag{1}
\]

The Bloch fiber is real at zero, so choose a real periodic eigenfield
\(\phi\), normalized to squared norm one per conventional cell. No
computation of this eigenfield is required for the existence argument.

## 2. A finite all-cell defect has an admissible positive eigenvalue

Take \(L\ge2\) conventional cells in each coordinate direction. Let
\(\chi_L\) select all electric-edge anchors in those cells and set
\(x_L=\chi_L\phi/L^{3/2}\). Then \(\|x_L\|=1\). Since the stencil radius
is two physical cells, the commutator \([H_0,\chi_L]\) acts only on the
one-conventional-cell boundary shell. The shell contains at most

\[
(L+2)^3-(L-2)^3=12L^2+16\le16L^2
\]

conventional cells. Its portion of the periodic eigenfield therefore has
norm at most \(4L\). The commutator has operator norm at most \(2J\),
which proves

\[
\|H_0x_L-\lambda x_L\|\le8J/\sqrt L.
\tag{2}
\]

For \(R_0=H_0^{-1}\), put \(r_L=H_0x_L-\lambda x_L\). Multiplying by
\(R_0\) gives the exact identity

\[
R_0x_L=\lambda^{-1}x_L-\lambda^{-1}R_0r_L.
\]

By (1), (2), and \(\|R_0\|\le1/g\),

\[
\langle x_L,R_0x_L\rangle
 >\frac{320}{59}-\frac{1024J}{g\sqrt L}.
\tag{3}
\]

For definiteness choose

\[
L=(45312J/g)^2
 =8818329545368141824.
\tag{4}
\]

The last error in (3) is at most \(4/177\); hence the Rayleigh quotient is
strictly greater than \(956/177\).

Let \(\mathcal D\) contain every scalar cell incident to any edge in the
support of \(x_L\); a cube of cell indices from \(-1\) through \(20L\),
inclusive, in each coordinate is sufficient in the usual edge-anchor Yee
indexing. With the coordinate-reflected indexing convention one may instead
use \([-2,20L+2]^3\), which is also sufficient and will be used below.
For the affected-edge selector \(Q\) and fractions \(W\), every edge of
\(x_L\) has \(W_{ee}=1\). Therefore the unit vector whose affected-edge
entries are \(x_L\) has Rayleigh quotient (3) for
\(S_0=W^{1/2}QR_0Q^*W^{1/2}\). In particular,

\[
\lambda_{\max}(S_0)>956/177>16/3.
\tag{5}
\]

This argument uses a full scalar-cell cube, not independent edge changes.
The boundary fractions are exactly the numbers of changed incident cells
divided by four, so the smallest positive fraction is \(1/4\).

## 3. A dyadic periodic perturbation makes the finite spectrum simple

Choose an integer \(P\), divisible by 20, greater than the defect cube's
side length by at least eight. Thus every affected electric edge and each
of its four incident scalar cells has a unique representative in one
period cell, with no wraparound collisions. A translate of the conventional
cell can always be selected to contain this finite set.

Enumerate scalar cells in that period cell by \(a=0,\ldots,P^3-1\), and
assign positive integers \(d_a=10^a\). Let \(D_d\) be their four-cell
averages at edges. If \(k_e\in\{1,2,3,4\}\) is the number of incident
defect cells at edge \(e\), then

\[
\frac{W_{ee}}{(D_d)_{ee}}
 =\frac{k_e}{\sum_{a\text{ incident to }e}10^a}.
\tag{6}
\]

These numbers are pairwise distinct for affected edges. Indeed two distinct
edges have different four-element incident-cell sets: such a set has one
constant coordinate and varies in the other two coordinates, identifying
the edge orientation, and then identifies its anchor. Equality in (6)
would make a nonzero integer polynomial in 10 vanish, whose coefficients
are between -4 and 4. Its leading nonzero term has greater absolute value
than the sum of all lower terms, since
\(4(1+10+\cdots+10^{r-1})<10^r\). This is impossible.

Let \(d_{\max}=10^{P^3-1}\) and consider the single-parameter family

\[
H(s)=H_0-tsD_d,\quad t=1/64,\qquad
S(s)=W^{1/2}QH(s)^{-1}Q^*W^{1/2}.
\]

It is analytic for \(|s|<g/(2td_{\max})\), by the inverse Neumann series.
It is also analytic throughout the upper half-plane. To see invertibility
there, write \(s=a+ib\), \(b>0\). The imaginary part of
\(\langle x,H(s)x\rangle\) has absolute value at least
\(tb\,d_{\min}\|x\|^2\). This bounds \(H(s)\) below, and the same
argument for its adjoint proves that its closed range is dense; hence it
is onto and its inverse norm is at most \((tb d_{\min})^{-1}\).

The upper half-plane together with the disk just specified is a connected
analytic domain. As \(T\to+\infty\), the operator-norm Neumann expansion
at \(s=iT\) gives

\[
S(iT)=\frac{i}{tT}
 \operatorname{diag}\!\left(\frac{W_{ee}}{(D_d)_{ee}}\right)
 +O(T^{-2}).
\tag{7}
\]

The leading diagonal entries are pairwise distinct by (6), so for all
sufficiently large \(T\) the eigenvalues are simple (for example, use
disjoint Gershgorin disks after multiplication by \(T\)). The discriminant
of the characteristic polynomial of \(S(s)\) is an analytic function,
nonzero at those points. It cannot vanish identically on any real interval
inside its domain: such an interval has an accumulation point in the
domain, contradicting the analytic identity theorem. Its zeros are isolated.

Consequently there is a positive dyadic \(s\) in

\[
0<s<\beta/d_{\max},\qquad \beta=g^2/(1024t)=2^{-28},
\tag{8}
\]

at which all eigenvalues of \(S(s)\) are simple. Set
\(\epsilon'_b=\epsilon_b+s d\). This is a dyadic scalar material with
\(1\le\epsilon'_b\le12+\beta\). Moreover

\[
\|H(s)-H_0\|\le t\beta=g^2/1024<g/2,
\quad \operatorname{dist}(0,\operatorname{spec}H(s))\ge g/2,
\]

and the resolvent identity yields

\[
\|S(s)-S_0\|
 \le\|H(s)^{-1}-R_0\|
 \le\frac{g^2/1024}{g(g-g^2/1024)}
 <1/512.
\tag{9}
\]

Equations (5) and (9) imply that the largest eigenvalue \(\mu\) of \(S(s)\)
is simple and greater than \(16/3\). This does not require positivity of
the remaining eigenvalues.

## 4. Effective selection and finite exact acceptance

The existence of a suitable dyadic \(s\) is effective. Enumerate positive
dyadics in (8), and dovetail the following finite test for increasing
integers \(\ell\). Put \(g'=g/2\) and choose a rational norm bound, for
example \(J'=17\). The finite-propagation polynomial

\[
P_\ell(H)=\frac{H}{(J')^2}
\sum_{j=0}^\ell\left(I-\frac{H^2}{(J')^2}\right)^j
\]

satisfies, by scalar spectral calculus,

\[
\|H^{-1}-P_\ell(H)\|
 \le (g')^{-1}
 \left(1-\frac{(g')^2}{(J')^2}\right)^{\ell+1}
 =:\eta_\ell.
\tag{10}
\]

The entries of \(T_\ell=QP_\ell(H)Q^*\) are computable by finitely many
exact rational operations on a finite neighborhood. The matrix
\(W^{1/2}T_\ell W^{1/2}\) is symmetric, and it is similar to the rational
matrix \(WT_\ell\). Thus exact rational polynomial arithmetic and real-root
isolation of \(\det(WT_\ell-zI)\) provide arbitrarily narrow certified
intervals for its eigenvalues, with multiplicities. No floating-point
eigensolver assertion is used.

Let \(d=\dim S\). Accept only when there are **exactly \(d\) real
root-isolation intervals, each certified to contain one root of algebraic
multiplicity one**; when all these intervals, each enlarged by
\(\eta_\ell\), are pairwise disjoint; and when one enlarged interval lies
strictly above \(16/3\). An interval containing a repeated root never passes.
Weyl's min-max inequality and (10) certify all true eigenvalues in these
intervals and certify simplicity. The positive distance between the
selected interval and all others is a rational separation bound.

At every dyadic parameter with simple true spectrum and largest eigenvalue
greater than \(16/3\), sufficiently large \(\ell\) passes this test. The
analytic argument proves that such parameters exist. Dovetailing therefore
terminates. This is a constructive definition of fixed material data and
fixed certified constants. Its actual execution is not asserted here.

The polynomial root-isolation step can equivalently be replaced by exact
rational inertia checks, using the congruence

\[
W^{1/2}(T_\ell-aW^{-1})W^{1/2}
 =W^{1/2}T_\ell W^{1/2}-aI.
\]

Both formulations avoid treating square roots of the weights as exact
rational numbers.

## 5. Tuning, material headroom, and the localized mode

Since \(\|S(s)\|\le\|H(s)^{-1}\|\le2/g\),

\[
g/2\le v_*=1/\mu<3/16.
\]

For \(|v-v_*|\le g/8\), therefore, \(v>0\) and

\[
\epsilon'_b+64v
 <12+\beta+12+8g<24.5.
\]

The change is applied to scalar cells; the induced edge change is exactly
\(vQ^*WQ\). Hence every such tuning is admissible and leaves headroom
\(1/2\). The sampling inequality is unchanged:
\(25/64<4\pi^2/100\), since \(\pi>25/8\).

If \(u\) is the normalized simple eigenvector at \(\mu\), define
\(E=H(s)^{-1}Q^*W^{1/2}u\). It is nonzero, and direct multiplication gives

\[
(H(s)-v_*Q^*WQ)E=0.
\]

Conversely every physical zero mode maps injectively to an eigenvector of
\(S(s)\) at \(\mu\). Thus the physical kernel is one-dimensional. For
localization use the bounded, boundedly invertible diagonal weights
\(F_R(x)=\exp(a\min\{\operatorname{dist}(x,\operatorname{supp}Q),R\})\).
Conjugating \(H(s)\) by \(F_R\) changes it in norm by at most
\(J'(e^{a r_H}-1)\), uniformly in \(R\), because the clipped distance is
1-Lipschitz. Choose fixed \(a>0\) making this at most \(g'/2\).
The inverse Neumann series gives
\(\|F_R H(s)^{-1}F_R^{-1}\|\le2/g'\) uniformly in \(R\).
Since \(F_R\) is identically one on the source support,
\(\|F_R E\|\le(2/g')\|Q^*W^{1/2}u\|\). Taking \(R\to\infty\) by
monotone convergence proves exponential weighted square summability and
therefore exponential localization of \(E\).

## Limitations relevant to continuation

* The original H1 certificate remains an external computational premise.
* The original defect's eigenvalue, simplicity, and listed couplings remain
  uncertified by this argument.
* The new generic supercell perturbation generally breaks cubic symmetry.
  An H3 argument that needs cubic symmetry must either tolerate this
  perturbation, use a different simplicity argument, or construct the
  defect and its coupling jointly.
* The proof does not turn exponential upper decay into a transmission lower
  bound. In particular it supplies no constants satisfying \(r^2<a\).
* No calculation on a feasible-size approximation has been labeled a
  certificate for the enormous fixed construction defined above.

