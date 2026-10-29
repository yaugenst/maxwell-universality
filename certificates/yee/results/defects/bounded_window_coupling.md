# Replacing all-distance coupling lower bounds by bounded-window selection

## Scope

This is an analytic sufficient lemma for the physical composition. It
removes one unnecessary burden in H3: a lower bound need not hold at every
large distance or on one fixed arithmetic progression. A fixed bounded
window of candidate distances, independently chosen in each coordinate
direction, is enough. The lemma does **not** establish the required Green
function asymptotics for an admissible Yee background. That remains open.

The proof also explains why oscillatory leading terms do not automatically
require a Diophantine estimate. Distinct exponential phases can be separated
by a fixed Vandermonde matrix over a bounded number of adjacent distances.

## 1. An elementary sequence lemma

Let \(z_1,\ldots,z_L\) be distinct nonzero complex numbers of the same
modulus \(\rho\in(0,1)\), and let \(c=(c_1,\ldots,c_L)\ne0\). Suppose
that a real sequence \(h(n)\), for integers \(n\ge n_0\), has the form

\[
h(n)=n^{-p}\left(\sum_{\ell=1}^{L}c_\ell z_\ell^n+e_n\right),
\qquad |e_n|\le C n^{-\sigma}\rho^n,
\tag{1}
\]

where \(p\ge0\), \(\sigma>0\), and all bounds and constants are certified
and effectively computable. The coefficients and roots may be non-rational;
certified approximation algorithms suffice. Faster exponentially decaying
remainders can be included in (1) by enlarging \(n_0,C\).

For the Vandermonde matrix \(V_{q\ell}=z_\ell^q\),
\(0\le q\le L-1\), let \(v>0\) be any certified lower bound on its least
singular value, and let \(c_*>0\) be a lower bound on \(\|c\|_2\). Such
bounds exist because the roots are distinct and \(c\ne0\). Define

\[
D_0\ge\max\left(n_0,L,
\left(\frac{2\sqrt L C}{v c_*}\right)^{1/\sigma}\right).
\tag{2}
\]

Then for every integer \(D\ge D_0\), at least one
\(q\in\{0,\ldots,L-1\}\) satisfies

\[
|h(D+q)|\ge
\frac{v c_*}{2^{p+1}\sqrt L}\,D^{-p}\rho^D.
\tag{3}
\]

**Proof.** Put \(a_\ell=c_\ell z_\ell^D\), so
\(\|a\|_2=\rho^D\|c\|_2\). The vector with components
\(\sum_\ell c_\ell z_\ell^{D+q}\) is \(Va\), whose norm is at least
\(v c_*\rho^D\). The remainder vector has norm at most
\(\sqrt L C D^{-\sigma}\rho^D\), since \(\rho^q\le1\). By (2), the
vector \(((D+q)^p h(D+q))_{q=0}^{L-1}\) therefore has norm at least
\(v c_*\rho^D/2\). One component has absolute value at least this norm
divided by \(\sqrt L\). Since \(D+q\le2D\), division by \((D+q)^p\)
proves (3). \(\square\)

For any certified \(a\) with \(0<a<\rho\), the polynomial prefactor can
be absorbed: by increasing the effective constant \(D_0\), (3) implies

\[
\max_{0\le q<L}|h(D+q)|\ge c_0 a^D
\qquad(D\ge D_0)
\tag{4}
\]

for a fixed, effectively computable \(c_0>0\). For example, select
\(b\in(a,\rho)\) and a threshold after which \(D^p\le(\rho/b)^D\);
then \(D^{-p}\rho^D\ge b^D\ge a^D\). A finite search with rational
enclosures of exponentials and logarithms can find such a threshold.

An explicit lower bound on \(v\) can avoid singular-value computation.
If \(|z_i-z_j|\ge s>0\) for all \(i\ne j\), then

\[
|\det V|\ge s^{L(L-1)/2},\qquad \|V\|_2\le\|V\|_F\le L,
\]

and hence
\(v=s^{L(L-1)/2}/L^{L-1}\) is valid. For \(L=1\), use \(v=1\).

## 2. A sufficient replacement for H3

Retain the full-block upper bound

\[
\|G(n)\|\le C_0 r^{\|n\|_1}\qquad(n\ne0),\quad0<r<1.
\tag{5}
\]

For each axis \(j\), suppose \(h_j(n)=u^T G(n e_j)u\) has a certified
expansion of the form (1), possibly with different finite numbers of roots,
powers, and constants. Suppose the leading root moduli satisfy

\[
r^2<\min_j\rho_j.
\tag{6}
\]

Choose a fixed rational \(a\in(r^2,\min_j\rho_j)\). The sequence lemma
provides fixed \(L_*\), \(D_*\), and \(c_*>0\), independent of the sparse
input, such that for every \(D\ge D_*\), one can select separately

\[
d_j\in\{D,\ldots,D+L_*-1\},\qquad
|h_j(d_j)|\ge c_*a^D\quad(j=1,2,3).
\tag{7}
\]

Use the physical translation lattice with basis
\(P d_1e_1,P d_2e_2,P d_3e_3\) instead of the isotropic spacing \(Pd\).
For any logical translation \(n\in\mathbb Z^3\),

\[
\|G((d_1n_1,d_2n_2,d_3n_3))\|
 \le C_0 r^{\sum_jd_j|n_j|}
 \le C_0(r^D)^{\|n\|_1}.
\tag{8}
\]

Thus every interaction sum in the conditional composition proof remains
valid with \(\zeta=r^D\), while intended couplings satisfy (7). Define
\(\alpha=(c_*/4)a^D\) and choose
\(D\) so that \(\zeta^2\le\alpha\). Each mediator still has two
identical signed incident couplings: both are translations by
\(\pm Pd_j e_j\), and symmetry gives \(h_j(-d_j)=h_j(d_j)\).
The exact mediator Schur complement is unchanged. All error estimates use
\((r^2/a)^D\), so \(D=O(1+\log\bar K+\log(1/\epsilon))\) remains
sufficient. The coordinate stretches here are geometric spacings between
defects, **not** PML coordinate stretches; the Yee operator remains entirely
unstretched with \(s=1\).

The lattice spacings differ from \(D\) by fixed constants. Every containing
rectangular domain therefore has the same asymptotic volume bound
\(\widetilde O(m^{3/2})\); no uncontrolled aspect ratio is introduced.

## 3. Certified finite-precision selection

For each axis compute all \(L_*\) candidate values \(h_j(D+q)\) to
absolute error at most \(\zeta^2\), using the finite-propagation inverse
polynomial and the isolated-mode calibration from the conditional proof.
Choose the candidate with greatest absolute computed value. By (7), its
computed magnitude is at least \(c_*a^D-\zeta^2\ge3\alpha\). Its actual
magnitude is at least \(c_*a^D-2\zeta^2\ge2\alpha\). Use the computed
signed value as \(-\beta_j\). In particular,

\[
|\beta_j|\ge3\alpha,
\quad |\beta_j+h_j(d_j)|\le\zeta^2,
\quad |\beta_j|\le(C_0+1)\zeta.
\]

These are exactly the estimates needed by the mediator construction. All
candidate sets have fixed size. Their distances are \(O(D)\), so selection
has only a fixed-factor cost relative to the original local calibration.

## 4. Why separate axial choices matter

There need not be one common distance good for every axis. For example,

\[
h_1(n)=\rho^n(1+(-1)^n),\qquad
h_2(n)=\rho^n(1-(-1)^n)
\]

have good values in every length-two window but never simultaneously at
the same \(n\). These exact sequences satisfy the finite-exponential-sum
premise. Independent \(d_1,d_2\) avoid this cancellation without changing
any scalar-material, physical-support, or conditioning requirement.

## 5. Remaining mathematical obligation

To use this lemma for the supplied or modified Yee background, one still
must prove a uniform asymptotic expansion, certify nonzero leading
coefficients for the actual defect mode, certify all relevant dominant
complex Bloch points and remainder estimates, and show (6). The finite
observed couplings do not supply these premises. The lemma addresses phase
cancellation **after** those spectral facts are established; it cannot
replace them.

