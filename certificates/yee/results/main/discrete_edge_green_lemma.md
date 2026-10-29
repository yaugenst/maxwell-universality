# A discrete simple-edge route to quantitative three-dimensional coupling

## Status and scope

This is an analytic conditional lemma for a finite-range, real, periodic,
self-adjoint lattice operator. Its problem-specific spectral hypotheses
are now supplied for the inversion-FCC Yee background by the accepted
finite certificates assembled in `../../theorem_and_proof.md`, Section 8,
and `global_edge_assembly_audit.md`. Those finite checks remain separate
dependencies of this general analytic lemma. The argument below treats the
finite-dimensional Bloch matrix directly; it does not transfer a continuum
elliptic theorem to the Yee operator.

The local defect construction used in the final section is proved in
`../logical/edge_mode_route.md`. In particular, it supplies a finite scalar
cell cluster and a simple compressed-resolvent eigenmode with a nonzero
overlap with the edge Bloch state for every sufficiently small positive
gap parameter. The constants and the cluster may be extremely large, but
are fixed independently of the sparse input.

## 1. Exact hypotheses

Write the operator using a fixed period lattice, so its Bloch matrix is

\[
H(k)=\sum_{\ell\in\mathcal F} H_\ell e^{i\ell\cdot k},\qquad
k\in\mathbb T^3,\quad H_{-\ell}=H_\ell^T\in\mathbb R^{s\times s},
\tag{1}
\]

with finite \(\mathcal F\subset\mathbb Z^3\). Assume the following facts
have been proved, with effective bounds.

1. A positive spectral endpoint \(E_c\) bounds a nonempty gap from above.
   All bands below it lie at most \(E_c-g_-\), for fixed \(g_->0\).
2. On the real Bloch torus, \(E_c\) is attained by exactly one band at
   exactly one point \(k_*\), modulo the period lattice. This eigenvalue
   is simple at \(k_*\). The point is a time-reversal invariant momentum:
   \(2k_*\in2\pi\mathbb Z^3\).
3. Its local analytic eigenvalue \(\lambda(k_*+q)\) has positive definite
   Hessian \(Q\). Thus
   \[
   \lambda(k_*+q)=E_c+\tfrac12q^TQq+O(|q|^4).
   \tag{2}
   \]
4. The finite Bloch matrix, the strict spectral inequalities, the
   eigenvalue/projector and their analytic neighborhoods have effective
   descriptions. For the dyadic Yee candidate, a finite exact interval
   certificate with strict margins would supply this information.

Uniqueness in item 2 is global, not merely a comparison of finitely many
symmetry points. It implies a positive spectral distance from \(E_c\)
on every compact set avoiding \(k_*\). This follows by continuity and
compactness, and is effective from a certified cover.

Shift \(k_*\) to zero in local formulas. Since \(e^{ik_*\cdot\ell}=\pm1\),
the shifted coefficients remain real. Simplicity and time reversal imply
the identities

\[
\lambda(-z)=\lambda(z),\quad
\overline{\lambda(\bar z)}=\lambda(z),\quad
H(z)^T=H(-z),
\tag{3}
\]

for the local analytic continuation. In particular, odd Taylor
coefficients of \(\lambda\) at zero vanish, \(\lambda(i\beta)\) is real,
\(\nabla\lambda(i\beta)\) is purely imaginary, and
\(\lambda''(i\beta)\) is real symmetric. These facts follow by uniqueness
of the analytic simple eigenvalue branch, and the identity theorem.

For \(0<\epsilon\ll1\), put

\[
E=E_c-\epsilon,\qquad R_\epsilon=(H-EI)^{-1}.
\tag{4}
\]

The scalar source associated with a finite real vector \(f\) has Bloch
transform \(\widehat f(k)\), a vector of Laurent polynomials. Its Green
coefficient at translation \(n\) is

\[
h_f(n)=\langle f,R_\epsilon T_n f\rangle
 =\frac1{(2\pi)^3}\int_{\mathbb T^3}e^{ik\cdot n}
 \widehat f(-k)^T(H(k)-E)^{-1}\widehat f(k)\,dk,
\tag{5}
\]

up to the immaterial convention replacing \(n\) by \(-n\). At a
time-reversal invariant point, the shifted \(\widehat f(k_*)\) is real.
Let \(P(k)\) denote the local analytic rank-one spectral projector and
define the analytic numerator

\[
A_f(k)=\widehat f(-k)^T P(k)\widehat f(k).
\tag{6}
\]

The shifts by \(k_*\) in (6) are understood modulo the torus. The
essential overlap hypothesis is \(A_f(k_*)>0\). Uniform versions for a
family of finite vectors are stated below.

## 2. A global complex contour giving the full-block upper bound

Fix \(\eta\in(0,1/100]\). For all sufficiently small \(\epsilon\), the
matrix \(H(k+i\beta)-E\) is invertible for every real \(k\), provided

\[
\|Q^{1/2}\beta\|\le(1-\eta)\sqrt{2\epsilon}.
\tag{7}
\]

To prove this, first work in a fixed real ball around \(k_*\). The simple
eigenvalue is separated from the complementary spectrum in a fixed complex
neighborhood. By (2)--(3), shrinking that neighborhood if necessary gives

\[
\operatorname{Re}(\lambda(q+i\beta)-E)
 \ge \epsilon-\tfrac12\beta^TQ\beta-C|\beta|^4+c|q|^2
 \ge c_\eta\epsilon+c|q|^2.
\tag{8}
\]

Here \(c,c_\eta>0\) and all neighborhood radii are effective. The mixed
Taylor remainders are absorbed into \(c|q|^2\), since all odd powers of
real \(q\) have purely imaginary coefficients when expanded at
\(i\beta\). On the compact complement of the real ball, the real matrix
is separated from \(E_c\). A small complex perturbation is therefore
invertible there by a Neumann estimate. This also bounds its inverse.
The local spectral decomposition and (8) give a uniform inverse bound
\(C_\eta/\epsilon\) on (7).

For a finite source block \(K\), its Bloch transform is a finite Laurent
matrix. Shifting the entire periodic Fourier integral through the line
\(s\beta\), \(0\le s\le1\), is valid. One need not shift the three
coordinates in a potentially inadmissible order: differentiating the
integral along this line gives the integral of a periodic total
derivative, which is zero. Consequently

\[
\|K^T R_\epsilon T_n K\|
 \le C_{\epsilon,\eta,K}
 \exp\!\left[-(1-\eta)\sqrt{2\epsilon}\,
                    \|Q^{-1/2}n\|\right].
\tag{9}
\]

Choose \(\beta\) in (7) maximizing \(\beta\cdot n\) to obtain (9).
This is an upper bound on the entire finite interaction block. The
constant includes the bounded growth of the finite Laurent source
matrices on the shifted torus. It is fixed after \(\epsilon\) and the
cluster are fixed.

## 3. The supporting imaginary point

Define the real analytic function

\[
F(\beta)=E_c-\lambda(i\beta)
 =\tfrac12\beta^TQ\beta+O(|\beta|^4).
\tag{10}
\]

Its Hessian is positive definite in a fixed neighborhood. For every
nonzero real vector \(v\), the strictly convex component
\(\{F(\beta)<\epsilon\}\) has a unique point \(\beta_v\) maximizing
\(v\cdot\beta\). It satisfies

\[
F(\beta_v)=\epsilon,\qquad
\nabla F(\beta_v)=\chi_v v,\quad\chi_v>0.
\tag{11}
\]

Uniformly in the direction of \(v\),

\[
I_v:=\beta_v\cdot v
 =\sqrt{2\epsilon}\,\|Q^{-1/2}v\|\,[1+O(\epsilon)].
\tag{12}
\]

For completeness, strict convexity follows from \(F''=Q+O(|\beta|^2)\).
The small level set is compact, smooth and strictly convex, so its support
point is unique. Comparing (10) with the two enclosing ellipsoids
\((1\pm c\epsilon)\beta^TQ\beta/2\) proves (12). The implicit function
theorem at the ellipsoidal support point, after scaling
\(\beta=\sqrt\epsilon\,b\), supplies effective error and derivative
bounds. Certified real analytic root isolation/Newton enclosures can
approximate \(\beta_v\) with arbitrarily small error.

Set \(Q_v=\lambda''(i\beta_v)\), which is real positive definite for
small \(\epsilon\). Let \(n_v=v/|v|\), and let \(S_v\) have two real
orthonormal columns spanning \(v^\perp\). Write

\[
Q_{v,\perp}=S_v^TQ_vS_v>0.
\tag{13}
\]

The determinant in (13) is independent of the chosen orthonormal basis.

## 4. Reaching the boundary contour is legitimate

For \(0\le s<1\), \(H(k+i s\beta_v)-E\) is invertible for all real
\(k\). Near \(k_*\), its potentially small denominator has

\[
\operatorname{Re}[\lambda(q+i s\beta_v)-E]
 \ge \epsilon-F(s\beta_v)+c|q|^2>0.
\tag{14}
\]

Outside that neighborhood the fixed complementary gap still applies.
Thus the global Fourier contour may be moved to \(s\beta_v\).
At \(s=1\), its only singular point is \(q=0\). By the local spectral
decomposition and (14), the inverse norm is bounded by
\(C(1+|q|^{-2})\), uniformly for \(s\) sufficiently close to one.
This function is locally integrable in dimension three. Dominated
convergence gives the boundary-contour identity

\[
h_f(dv)=e^{ik_*\cdot dv-I_vd}\frac1{(2\pi)^3}
 \int_{\mathbb T^3} e^{idv\cdot q}
 \widehat f(-k_*-q-i\beta_v)^T
 [H(k_*+q+i\beta_v)-E]^{-1}
 \widehat f(k_*+q+i\beta_v)\,dq.
\tag{15}
\]

This step is essential. Smooth localization is performed only after the
whole resolvent has reached this contour. Therefore even the smooth
remainder retains the factor \(e^{-I_vd}\). Localizing on the original
real torus and calling a merely smooth remainder exponentially small
would not be valid.

## 5. Direct pole and Gaussian calculation

Use local orthonormal coordinates \(q=u n_v+S_vw\), \(w\in\mathbb R^2\).
Let

\[
D(u,w)=\lambda(i\beta_v+u n_v+S_vw)-E.
\tag{16}
\]

At the origin, \(D=0\), \(D_w=0\), and
\(D_u=i c_v\), where \(c_v=\chi_v|v|>0\). The analytic implicit
function theorem gives the unique nearby root \(u=p(w)\), with

\[
p(w)=\frac{i}{2c_v}w^TQ_{v,\perp}w+O(|w|^3),\qquad
\operatorname{Im}p(w)\ge c'|w|^2.
\tag{17}
\]

The second inequality follows by choosing a sufficiently small fixed
neighborhood. The symmetry in (3) gives
\(p(-w)=-\overline{p(w)}\); in particular the quadratic term in (17)
is purely imaginary and positive.

Factor \(D(u,w)=(u-p(w))d_1(u,w)\), with \(d_1\) analytic and nonzero.
Cauchy division of the numerator gives

\[
\frac{A_f(i\beta_v+u n_v+S_vw)}{D(u,w)}
 =\frac{a(w)}{u-p(w)}+g(u,w),
\quad a(0)=\frac{A_f(i\beta_v)}{i c_v},
\tag{18}
\]

where \(g\) and \(a\) are analytic. Take smooth compactly supported
cutoffs \(\chi_1(u),\chi_2(w)\), both one near zero, inside this chart.
Choose the support of \(\chi_2\) sufficiently small that every \(p(w)\)
lies strictly inside the core where \(\chi_1=1\), for example with
\(|p(w)|\) less than half the core radius.
The rest of the integrand in (15), including \(\chi_1\chi_2g\), is
smooth on the torus. Repeated integration by parts along \(v\) bounds
its Fourier coefficient by \(C_M d^{-M}\) for every fixed integer
\(M\).

Put \(T=d|v|>0\). For real \(w\ne0\) in the support,
\(\operatorname{Im}p(w)>0\), so closing the one-dimensional contour in
the upper half-plane gives

\[
\int_{\mathbb R}\frac{e^{iTu}}{u-p(w)}\,du
 =2\pi i e^{iTp(w)}.
\tag{19}
\]

The value at \(w=0\) is irrelevant to the two-dimensional integral.
The integral in (19) is an improper oscillatory integral. For truncation
at \(|u|=R\), integration by parts bounds its omitted tails by
\(C/(TR)\), uniformly for the bounded set of poles under consideration.
The original localized three-dimensional integral is absolutely
integrable by (14). Thus one may first use finite truncations and then
pass to (19) under the compact \(w\) integral using that uniform tail
bound; no exchange of conditionally convergent integrals is assumed.
Replacing the full-line integrand in (19) by its product with \(\chi_1\)
has error \(O(T^{-M})\), uniformly in \(w\): every positive-order
derivative of \((1-\chi_1(u))/(u-p(w))\) is integrable, uniformly because
the removed region stays away from \(p(w)\). Integration by parts proves
the claimed bound, with no unproved contour truncation assumption.

The singular contribution is consequently

\[
2\pi i\int_{\mathbb R^2}\chi_2(w)a(w)e^{iTp(w)}\,dw+O(T^{-M}).
\tag{20}
\]

Equation (17), Taylor expansion of \(a\), and the change of variables
\(w=T^{-1/2}z\) give

\[
\int \chi_2(w)a(w)e^{iTp(w)}\,dw
 =a(0)\frac{2\pi c_v}{T\sqrt{\det Q_{v,\perp}}}
   +O(T^{-3/2}).
\tag{21}
\]

This remainder has an elementary absolute estimate: the amplitude error
is bounded by \(C|w|\), and the exponent error by
\(CT|w|^3\), against \(e^{-cT|w|^2}\) after shrinking the chart. Their
two-dimensional integrals are respectively \(O(T^{-3/2})\) and
\(O(T^{-3/2})\). The removed Gaussian tails are exponentially small.
All constants are bounded by finitely many analytic derivative bounds.

Combining (15), (18), (20), and (21) proves

\[
\boxed{
h_f(dv)=e^{ik_*\cdot dv-I_vd}
 \left[
 \frac{A_f(i\beta_v)}{2\pi d|v|\sqrt{\det Q_{v,\perp}}}
 +O(d^{-3/2})\right].}
\tag{22}
\]

This is an all-large-integer-distance theorem, with an effective
remainder, for each fixed nonzero integer translation \(v\).
If \(A_f(i\beta_v)>0\), its leading coefficient cannot cancel. Since
\(k_*\) is a time-reversal invariant momentum,
\(e^{ik_*\cdot dv}\in\{1,-1\}\); its sign has no effect on the required
absolute lower bound.

## 6. Uniformity for the selected scalar defect mode

Let a fixed finite cell cluster have edge weights \(W\), edge restriction
\(Q_0\), and selected real unit mode \(u_\epsilon\). Use
\(f_\epsilon=Q_0^T W^{1/2}u_\epsilon\). Suppose

\[
|w^T u_\epsilon|\longrightarrow c_*>0,
\qquad w=W^{1/2}Q_0\phi_*,
\tag{23}
\]

where \(\phi_*\) is the normalized Bloch edge state extended over the
cluster. For a fixed cluster, the finite Laurent source transform and
the analytic projector imply a bound

\[
|A_f(k_*+z)-A_f(k_*)|\le C_K|z|
\tag{24}
\]

uniformly over every real unit \(u\) used to form \(f\). The constant is
effective, although it can grow rapidly with cluster diameter. Since
\(|\beta_v|=O(\sqrt\epsilon)\) uniformly over directions, (23)--(24)
give \(A_{f_\epsilon}(i\beta_v)>c_*^2/4\) for every direction and all
sufficiently small \(\epsilon\). Thus (22) applies simultaneously to
any three fixed integer basis vectors.

The rank-one edge expansion and branch-splitting proof in
`../logical/edge_mode_route.md` provides precisely (23). Its choice of a
large all-cell cluster also makes the resonance sufficiently weak to
leave scalar material headroom. Choosing the final uniform material
shift dyadic makes the physical background dyadic; \(\epsilon=E_c-E\)
itself need not be dyadic. All choices are fixed before the sparse input
is read.

## 7. Integer whitening supplies the strict rate inequality

For fixed \(\eta=1/100\), choose an invertible integer matrix \(B\) by
rounding \(M Q^{1/2}\), for a sufficiently large fixed integer \(M\).
Effective spectral enclosures let one verify

\[
M(1-\eta)\|x\|\le\|Q^{-1/2}Bx\|
 \le M(1+\eta)\|x\|\quad(x\in\mathbb R^3).
\tag{25}
\]

For example, certified entry approximations allow an integer choice with
entry errors at most one, without deciding an exact nearest-integer tie.
The rounding error then has norm at most three, so any
\(M\) making \(3\|Q^{-1/2}\|/M<\eta\) suffices. The matrix is then
automatically nonsingular. It can be made larger still to accommodate a
fixed cluster and lattice convention.

After choosing \(\epsilon\) sufficiently small, (9), (12), and (25)
give the upper exponent

\[
U=\frac{(1-\eta)^2}{\sqrt3}\sqrt{2\epsilon}\,M
\tag{26}
\]

per unit of \(\ell^1\) translation in the \(B\)-lattice, while all
three axial lower-bound exponents satisfy

\[
I_{Be_j}\le V=(1+\eta)^2\sqrt{2\epsilon}\,M.
\tag{27}
\]

The exact inequality
\(2(1-\eta)^2/\sqrt3>(1+\eta)^2\) holds at \(\eta=1/100\).
Hence choose fixed rational \(r,a\in(0,1)\) such that

\[
e^{-U}<r<\sqrt a,\qquad a<e^{-V}.
\tag{28}
\]

Equation (9) gives the full-block upper estimate
\(\|G(Bn)\|\le C_0r^{\|n\|_1}\). Equations (22)--(24) give
\(|u^TG(dBe_j)u|\ge c d^{-1}e^{-I_{Be_j}d}\) beyond an effective
threshold, simultaneously for \(j=1,2,3\). Since \(a<e^{-V}\), increasing
that threshold absorbs \(d^{-1}\), proving

\[
\|G(Bn)\|\le C_0r^{\|n\|_1},\qquad
|u^TG(dBe_j)u|\ge c' a^d,\qquad r^2<a.
\tag{29}
\]

This is the required useful coupling, on a fixed skew sublattice of
period translations. It changes physical defect placement, not the Yee
coordinate metric or stretch. All coordinate stretches remain one.

## 8. Effectivity and volume

Every strict inequality used above is stable. The finite Bloch matrix
has explicit Laurent coefficients. Local simple eigenvalue bounds,
derivative estimates, resolvent bounds on compact complements,
implicit-function neighborhoods, the finite cluster and its mode,
\(B,r,a,C_0,c',d_0\) can therefore be obtained by finite searches with
rational enclosures, once hypotheses 1--4 are certified. The searches
terminate by the strict margins proved above. They are fixed
preprocessing; they are not an input-dependent spectral solve.

The logical routing proof uses a balanced containing cube of side
\(O(\sqrt{m\log m})\). Multiplication of its coordinates by the fixed
integer matrix \(B\), and then by the fixed physical period lattice,
enlarges every side of a containing rectangular box by a fixed factor.
After the usual logarithmic defect spacing and buffer, the number of
physical cells remains \(\widetilde O(m^{3/2})\). Such a statement would
not follow merely from volume for an arbitrarily elongated logical
layout; the balanced layout is used here explicitly.

## 9. Application to the certified Yee background

The finite local and global certificates now establish the Section 1
hypotheses for the exact inversion-symmetric FCC material. In conventional
period-20 radian coordinates, its unique edge is simple at
\(k_*=(\pi,\pi,\pi)\), its Hessian exceeds \(I/12000\), and one may use
\(g_-=1/128\) and scalar headroom \(h_{\rm mat}=12\). The proof of the
coordinate folding, global comparison, and effective analytic bounds is
in `global_edge_assembly_audit.md` and the master theorem.

This lemma and `../logical/edge_mode_route.md` therefore supply the fixed
defect/coupling data for the physical composition. The selection searches
are proved terminating and independent of the sparse input; they are not
represented as executed defect computations. The final clean combined
reproduction gate and the separately conditional randomized-SLTH
consequence are recorded in the master proof and obligation ledger.
