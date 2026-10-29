# Round 6: a certified resolved-regime three-dimensional Yee bulk gap

## Result and scope

**Theorem L1-20.** Use scalar cell permittivities and arithmetic averaging of the four incident cells at each electric edge. Let the conventional cubic period be 20 cells, the uniform grid spacing be 1, and the eight sphere centers in one conventional cell be

\[
20\bigl(F\pm(1/8,1/8,1/8)\bigr)\pmod {20},\qquad
F=\{(0,0,0),(0,1/2,1/2),(1/2,0,1/2),(1/2,1/2,0)\}.
\]

A cell has permittivity 12 if its center lies in the closed union of the radius-5 spheres, and permittivity 1 otherwise. Membership in this union is evaluated by the integer rule specified below, including equality at sphere boundaries. Let C be the unstretched infinite Yee curl and D the resulting diagonal electric material matrix. Then

\[
\boxed{\operatorname{dist}\bigl(0,\operatorname{spec}(C^*C-D/64)\bigr)\ge 1/4096.}
\]

This is a gap for the full electric operator, including its longitudinal sector. It is not a conclusion based only on sampled transverse eigenvalues. It is a bulk statement on the infinite periodic lattice, not a claim that every finite termination inherits the same gap.

The operating parameters h=1, omega=1/8, epsilon_min=1, epsilon_max=25, p_min=10, s_max=1 obey the physical-region sampling requirement. This construction uses no stretching, no structure in PML, and no sources in PML. The stated epsilon_max leaves room for subsequent defects, but this theorem by itself does not certify any such defect.

The proof consists of analytic reductions and 604 finite, exact-interval Bloch-box checks. Every box check covers all Bloch parameters in the box and every squared frequency in [63/4096,65/4096]. The remaining region near Gamma is handled analytically. The exact cover and all 48 required geometric symmetries are separately checked by integer arithmetic.

**What is not proved here:** an isolated tunable defect mode, a programmable wire or junction family, (B'), its amended-class SLTH conclusion, or (A).

## 1. Exact geometry, material convention, and sampling

For a cell index i in {0,...,19}^3, scale its center by eight:

\[
X_i=8i+(4,4,4).
\]

The scaled sphere centers are

\[
\mathcal C=\{(0,0,0),(0,80,80),(80,0,80),(80,80,0)\}\pm(20,20,20)
\pmod {160}.
\]

Reduce each coordinate of X_i-c to [-80,80), and set epsilon_i=12 exactly when the minimum squared distance to a c in this set is at most 1600. Otherwise set epsilon_i=1. These tests involve only small integers. There are exactly 3928 high-permittivity cells per conventional cell, and 982 per FCC primitive cell.

At an electric edge in direction j, D assigns the average of the four incident scalar cells. Therefore the possible entries of D are

\[
1,\quad15/4,\quad13/2,\quad37/4,\quad12.
\]

No electric component is independently programmable in this definition.

The exact integer label array is invariant under the FCC translations (0,10,10), (10,0,10), and (10,10,0). For every signed coordinate permutation R, the verifier finds an integer translation T with components in {0,5,10,15} and checks all 8000 labels under the corresponding cell-center map. Reflection of a cell center i+1/2 maps its integer index to -i-1. These checks certify the scalar material symmetries. They also certify the Yee operator symmetries: a cubical-complex automorphism permutes oriented edges and faces, with orientation signs, and intertwines their incidence matrix; arithmetic incident-cell averaging commutes with that permutation. Translation changes a Bloch field by a unit-modulus gauge factor and hence preserves its spectrum.

At t=omega^2=1/64,

\[
t\,\epsilon_{\max}=25/64<\pi^2/25=4\pi^2/p_{\min}^2.
\]

The inequality is verified with an outward rational enclosure of pi. Equivalently, the shortest permitted wavelength has 16 pi / 5 > 10 grid points. The chosen background uses only values 1 and 12; 25 is the allowed material upper bound, not an artificial rescaling of the grid.

## 2. Primitive cell, Fourier coordinates, and complete Brillouin-zone reduction

Use the primitive translations

\[
a_1=(20,0,0),\quad a_2=(10,10,0),\quad a_3=(10,0,10).
\]

A primitive cell has 2000 scalar cells and 6000 electric or magnetic coordinates. Write Cartesian Bloch wavevectors as (2 pi/20) kappa. Reciprocal lattice vectors in kappa coordinates have either all even or all odd integer components. A Voronoi Brillouin zone is

\[
\mathcal B=\{\kappa: |\kappa_i|\le1,\ |\kappa_1|+|\kappa_2|+|\kappa_3|\le3/2\}.
\]

To check that no reciprocal inequalities are missing, the Voronoi inequality for a reciprocal q is 2 kappa dot q <= |q|^2. For q=2m, the coordinate bounds give

\[
2\kappa\cdot q\le4\sum |m_i|\le4\sum m_i^2=|q|^2.
\]

For an all-odd q, write |q_i|=1+2b_i with nonnegative integers b_i. The two displayed restrictions on kappa give

\[
2\kappa\cdot q\le3+4\sum b_i\le\sum(1+2b_i)^2=|q|^2.
\]

Conversely, q=2e_i and q with all components +/-1 give the displayed facets. Thus the stated polytope is exactly the Voronoi cell. The 48 signed permutation symmetries reduce it to

\[
\mathcal W=\{0\le\kappa_3\le\kappa_2\le\kappa_1\le1,
\quad\kappa_1+\kappa_2+\kappa_3\le3/2\}.
\]

The Fourier representatives on the primitive cell are

\[
q=(n_1,2n_2-n_1,2n_3-n_1)\pmod {20},
\quad 0\le n_1<20,\quad0\le n_2,n_3<10.
\]

For each q define

\[
d_j(q,\kappa)=\exp\bigl(2\pi i(q_j+\kappa_j)/20\bigr)-1,
\quad l(q,\kappa)=\sum_j|d_j|^2.
\]

In this Fourier basis C is the cross-product matrix of d. Hence

\[
C C^*=l I-g g^*,\qquad g=\overline d,
\]

or, without ambiguous component notation, C C^*=l(I-P), where P is the orthogonal projector onto the vector g=conjugate(d). The electric curl-curl matrix has the corresponding one-dimensional gradient kernel and two nonzero eigenvalues l. All transforms used in the certificate are the exact finite Fourier transforms for these representatives. The implementation computes them as a unitary 20-by-10-by-10 twisted FFT; it is not a continuum or plane-wave approximation.

## 3. Magnetic formulation and why it proves the electric statement

Let

\[
B(\kappa)=C(\kappa)D^{-1}C(\kappa)^*.
\]

For kappa away from Gamma, let P(kappa) be the direct sum of the projectors onto g(q,kappa). It is exactly the kernel projector of B. Put

\[
A(\kappa,t')=B(\kappa)+2tP(\kappa)-t'I,
\quad t=1/64,\quad |t'-t|\le\sigma:=1/4096.
\]

On the gradient subspace its eigenvalue is 2t-t'>0. On the transverse subspace it is B-t'I. Thus invertibility of this auxiliary matrix throughout the indicated parameter set excludes all nonzero magnetic eigenvalues in [t-sigma,t+sigma]. Gamma is handled independently in Section 4.

Set T=C D^{-1/2}. The positive eigenvalues of T*T and TT* coincide, including multiplicity: for a positive eigenvalue lambda, T and T* map the two eigenspaces bijectively, with inverses T*/lambda and T/lambda. The zero eigenvalues of T*T are below t-sigma. Consequently the magnetic exclusion gives

\[
\|(D^{-1/2}C^*CD^{-1/2}-tI)^{-1}\|\le1/\sigma.
\]

Since D>=I,

\[
(C^*C-tD)^{-1}
=D^{-1/2}(D^{-1/2}C^*CD^{-1/2}-tI)^{-1}D^{-1/2}
\]

has norm at most 1/sigma. The bound is uniform over Bloch parameter. The lattice Fourier transform over primitive cells is unitary, and conjugates the infinite periodic operator to multiplication by these finite Bloch matrices. Applying their uniformly bounded inverses pointwise gives a bounded inverse of norm at most 1/sigma. For a bounded self-adjoint operator that is precisely the claimed spectral-distance bound.

## 4. The analytic Gamma region

Consider |kappa_i|<=3/16. For q=0,

\[
l(0,\kappa)\le a_0:=12\sin^2(3\pi/320).
\]

Every other reciprocal representative is either all odd or all even. In the odd case each reduced coordinate has distance at least 13/16 from an integer multiple of 20, giving

\[
l(q,\kappa)\ge a_1:=12\sin^2(13\pi/320).
\]

In the nonzero even case at least one coordinate has distance at least 29/16, giving

\[
l(q,\kappa)\ge a_2:=4\sin^2(29\pi/320).
\]

The use of the nearest representative is legitimate because sin^2(pi x/20) is increasing in |x| for |x|<=10.

There are exactly N+2 low electric curl-curl eigenvalues, counting the N longitudinal zeros and the two q=0 transverse values (at Gamma all N+2 are zero). The others are at least min(a_1,a_2). Since I<=D<=12I, eigenvalue comparison for the shifted electric matrix gives no zero eigenvalue whenever

\[
a_0<t-\sigma,\qquad a_1>12(t+\sigma),\qquad a_2>12(t+\sigma).
\]

The accompanying interval program verifies all three strict inequalities. This handles the entire Gamma cube, including its singular projector point, without numerically discarding any zero modes.

## 5. Bloch-box verification lemma

This section states every bound used by the interval verifier and derives the test. All constants are fixed rational witness bounds, verified at a box center; none is inferred from a sampled eigenvalue plot.

### 5.1 Decomposition and center data

Fix a center kappa_0 not equal to Gamma and a closed box |kappa_j-kappa_0j|<=h_j. Put

\[
c=2\pi/20,\quad s=c\sqrt{\sum_jh_j^2}.
\]

Choose a finite set of low Fourier representatives. Let L and Q be the coordinate projectors onto the low and high sets. Denote center quantities by subscripts 0.

The witness F=[F_-,F_+] consists of two negative columns and 2 n_low-2 positive columns. The stored dyadic raw columns are projected exactly with I-P_0; therefore F is exactly center-transverse. The interval verifier proves that LF has full column rank. Add the low gradient columns G: for each low q the column is 8 g_0(q)/sqrt(l_0(q)), supported only at q. The columns [F,G,Q] consequently form a basis of all 6000 coordinates. No high or longitudinal degree of freedom is omitted.

Write A_0=B_0+2tP_0-tI. The verified center inequalities are

\[
F_-^*A_0F_-\preceq-p_0I,\quad
F_+^*A_0F_+\succeq p_0I,\quad
G^*A_0G=I,\quad F^*A_0G=0,
\quad p_0=1-2^{-10}.
\]

The last two equalities follow exactly from C_0*G=0, F*G=0, G*G=64I, and 64t=1.

The verifier encloses the following center norms; their names match the code:

- nu_j=||F_j|| and e_j=||C_0*F_j||, for j=-,+,G (F_G means G);
- k_{j,a}=||F_j* B_a F_j||, for j=-,+;
- x_a=||F_+* A_a G||;
- u_{j,a}=||w Q A_a F_j||, where w(q)=(l_0(q)/12-t)^(-1/2) on the high set;
- rho_j=||Q A_0 F_j||, qnu_j=||QF_j||, qw_j=||wQF_j||;
- W_-=||l_0^(-1/2)F_-||^2 and W_+=||L l_0^(-1)F_+||;
- r<=min_q sqrt(l_0(q)), r_h<=min_high sqrt(l_0(q)), and l_0<=ell_cut on the low set.

Derivatives here are with respect to Cartesian kappa, at the center. For G, its exact high support and center residual are zero. Any nonzero bounds stored for these quantities are harmless overestimates.

### 5.2 Elementary perturbation inequalities

Let delta C=C(kappa)-C_0. The elementary scalar identities for exp(ix) give

\[
\|\delta C\|\le s,\qquad
\|\delta C-\sum_a(\kappa_a-\kappa_{0a})C_a\|\le s^2/2.
\]

Indeed |exp(ix)-1|<=|x| and |exp(ix)-1-ix|<=x^2/2 follow by one and two integrations of exp(ix). The Euclidean bounds on the three components give the stated cross-product operator bounds.

Since ||D^-1||<=1, for a fixed block F_j the remainder after the linear term in F_j*B(kappa)F_j has norm at most

\[
s^2(\nu_j e_j+\nu_j^2).
\]

For the mixed compression F_+*B(kappa)G, the same expansion and C_0*G=0 give remainder at most

\[
8s^2(e_+/2+\nu_+).
\]

Here and below t' shifts by at most sigma.

For completeness, the required projector remainder can be obtained directly. At one Fourier mode write v=g_0, w=g-g_0, w_1=sum x_a g_a, r_0=||v||. Then ||w||<=s and ||w-w_1||<=s^2/2. For f perpendicular to v,

\[
P(g)f=\frac{(v+w)w^*f}{|v+w|^2},\qquad
P'_1f=\frac{v w_1^*f}{r_0^2}.
\]

Furthermore

\[
\left\|\frac{v+w}{|v+w|^2}-\frac{v}{r_0^2}\right\|
\le \frac{s(3+s/r_0)}{(r_0-s)^2}.
\]

Subtract the two displayed formulas, first replacing w_1 by w and then changing the prefactor. This gives

\[
\|(P-P_0-P'_1)f\|
\le s^2\left[\frac1{2r_0}+\frac{3+s/r_0}{(r_0-s)^2}\right]\|f\|.
\tag{PR}
\]

It also gives ||P(g)f||<=s||f||/(r_0-s). For the old gradient direction, ||(I-P(g))v||<=s, by applying I-P(g) to v=(v+w)-w.

The negative diagonal projector contribution is consequently at most

\[
\frac{2ts^2 W_-}{(1-s/r)^2}.
\]

The positive diagonal projector contribution is positive semidefinite and can be dropped in a lower bound. The gradient compression loses at most 2s^2/r^2+64sigma from its center value 1.

Using (PR), Hermitian symmetry, G*G=64I, and its low-mode support, the mixed projector remainder is at most

\[
16t s^2 C_P W_+,\qquad
C_P=\frac{3+s/r}{(1-s/r)^2}+\frac{\sqrt{\ell_{\rm cut}}}{2(1-s/r)}.
\]

To see the weighting, multiply (PR) by r_0^2 and by the norm 8 of the normalized gradient columns. The resulting coefficient is bounded by (3+s/r)/(1-s/r)^2+sqrt(ell_cut)/2, which is no larger than the displayed C_P. This proves the stated bound without an estimate of the full derivative of a varying orthonormal basis.

### 5.3 High-block positivity and its Schur correction

D^-1>=I/12 and C C*=l(I-P) give

\[
Q A(\kappa,t')Q\succeq
Q\{(l/12-t')(I-P)+(2t-t')P\}Q.
\]

The right-hand side is positive if

\[
s<r_h,\quad b_h'= (r_h-s)^2/12-t-\sigma>0,
\quad t-\sigma>0.
\]

Put

\[
b_h=r_h^2/12-t,\quad
\chi=\sqrt{b_h/b_h'},\quad
w_*=b_h^{-1/2},\quad c_*=r_hw_*.
\]

On the high set, the shifted transverse inverse weight is at most chi times the center weight w. This follows because, for x>=r_h,

\[
\frac{x^2/12-t}{(x-s)^2/12-t-\sigma}
\]

is decreasing. Its derivative has numerator proportional to

\[
-sx(x-s)-12\sigma x-12ts<0.
\]

Also ||w Q C_0||<=c_* because x/sqrt(x^2/12-t) is decreasing for x^2>12t.

By (PR), the high projector remainder is bounded using

\[
K_P=\frac{r_h/2+3+s/r_h}{(r_h-s)^2}.
\]

The expression as a function of r_h decreases on r_h>s; differentiating its numerator and denominator verifies this, or expanding the derivative gives a sum with negative sign. The term 1/(2r_0) in (PR) was enlarged to r_0/[2(r_0-s)^2] for this bound.

For j=+,G define

\[
M_j=(w_* e_j+c_*\nu_j)/2+w_*\nu_j
+2tw_*K_Pq\nu_j.
\]

The last summand is omitted for G, whose projector and support remain low in Fourier index. Expansion of B=C D^-1 C* gives this bound for the center-weighted high remainder: the two linear-remainder terms contribute s^2(w_*e_j+c_*nu_j)/2, and the product of increments contributes s^2w_*nu_j.

It follows that the weighted high residual has norm at most

\[
R_j=\chi\left[w_*\rho_j+\sum_a h_a u_{j,a}+s^2M_j+\sigma qw_j\right].
\]

The longitudinal component has a sharper exact identity:

\[
P Q A(\kappa,t')F_j=(2t-t')P QF_j.
\]

Since center-transverse F_j has ||P QF_j||<=s qnu_j/(r_h-s), its contribution to the high Schur correction is bounded by

\[
(t+\sigma)s^2(q\nu_j)^2/(r_h-s)^2.
\]

Thus each high-block Schur correction is at most

\[
\eta_j=R_j^2+(t+\sigma)s^2(q\nu_j)^2/(r_h-s)^2.
\]

The mixed high Schur correction is at most sqrt(eta_+ eta_G), by Cauchy--Schwarz in the positive high inverse. This remains true though R_j overestimates the transverse residual by including some longitudinal part.

### 5.4 The four scalar tests

Collect the losses

\[
\begin{split}
\ell_-={}&\sum_a h_a k_{-,a}+s^2(\nu_-e_-+\nu_-^2)
+\frac{2ts^2W_-}{(1-s/r)^2}+\sigma\nu_-^2,\\
\ell_+={}&\sum_a h_a k_{+,a}+s^2(\nu_+e_++\nu_+^2)
+\sigma\nu_+^2,\\
\ell_G={}&2s^2/r^2+64\sigma,\\
e_b={}&\sum_a h_a x_a+s^2[8(e_+/2+\nu_+)+16t C_PW_+].
\end{split}
\]

After eliminating the positive high block, the negative diagonal block remains at most -(p_0-ell_-)I. Subtracting a positive semidefinite Schur correction only makes that negative block more negative.

The remaining physical-positive and gradient-positive blocks have diagonal lower bounds

\[
p=p_0-\ell_+-\eta_+,\qquad g=1-\ell_G-\eta_G,
\]

and cross norm at most e=e_b+sqrt(eta_+eta_G). They form a positive definite block if

\[
\boxed{p_0-\ell_->0,\quad p>0,\quad g>0,\quad pg-e^2>0.}
\tag{BOX}
\]

Indeed their quadratic form is at least p||x||^2+g||y||^2-2e||x||||y||, positive under these tests. Finally eliminate the negative block: its inverse is negative definite, so its elimination adds a positive semidefinite matrix to this positive block. Thus the whole auxiliary matrix is invertible, with exactly two negative eigenvalues. This proves the box lemma and accounts for every coordinate and every Schur complement.

## 6. Exact interval computation and finite covering

### 6.1 Arithmetic model

The acceptance calculations use rational-endpoint interval arithmetic only. The C++ kernel stores a complex rectangle as (x,y,r), meaning real and imaginary centers x/2^52 and y/2^52 with radius r/2^52 in each component. Products use signed 128-bit intermediate integers and an outward radius. All accumulations that could overflow have explicit range or overflow checks. Real divisions require a strictly positive denominator interval; integer square roots give outward square-root endpoints. Hermitian positive-definiteness tests use interval symmetric elimination with strictly positive pivot lower bounds. They do not accept a matrix on the basis of a floating eigenvalue.

The Python scalar interval layer uses 100-bit dyadic endpoints and arbitrary-size integers. Pi is enclosed using 16 arctan(1/5)-4 arctan(1/239), 120 alternating terms for each arctangent, and the next-term remainder bound. Roots of unity are enclosed by Taylor sums with |argument|<4 and explicit factorial remainder bounds. The FFT consists only of these interval additions, products, and square-root normalization factors.

Floating-point calculations are used to propose the raw Fourier columns and numerical bounds. The raw columns, after quantization, define exact dyadic witnesses; they are not assumed to approximate any eigenvector. The exact transverse projection, full-rank test, all operator-norm tests, and (BOX) are subsequently checked in intervals. A poor proposed witness makes the checker fail rather than invalidate its logic.

The point verifier checks the center compressions and all norms in Section 5 using Gram matrices and interval positive-definite elimination. A claimed upper bound ||X||<=b is checked by proving b^2 I-X*X positive definite. A claimed Hermitian operator norm is checked by proving both bI-X and bI+X positive definite. Analytic identities supply only exact quantities such as ||G||=8 and C_0*G=0.

### 6.2 Cover

All 604 verified boxes have halfwidth 1/32 and centers with odd numerator over 32. Their proposed Fourier low sets contain between 10 and 15 representatives (the machine manifest is authoritative). Every interval check covers the complete box, not just its intersection with the wedge, and all t' in [63/4096,65/4096].

The separate coverage checker recursively bisects [0,1]^3 using exact dyadic rational endpoints. A box can be discarded only after an exact feasibility test against the wedge. For box lower and upper endpoints lo,hi, the minimal potentially feasible ordered point is

\[
z=lo_3,\quad y=\max(lo_2,z),\quad x=\max(lo_1,y).
\]

The intersection is nonempty exactly when these values do not exceed the corresponding upper endpoints and x+y+z<=3/2. This is sufficient because they themselves then form a feasible point, and necessary because every feasible point is coordinatewise at least these values.

A remaining box is accepted only if entirely contained in the analytic Gamma cube, or if its exact center and halfwidth match an interval-certified box. Otherwise it is subdivided. The final exact counts are 604 certified boxes, 13 analytic Gamma boxes, 476 discarded boxes, and 156 subdivided internal nodes. All required leaves are covered, and the certificate has no unused or overlapping leaf records. SHA-256 hashes bind the point records to their witness files.

### 6.3 Actual output

The exact scalar consequences of all point certificates have lower bounds

\[
p_0-\ell_->1/128,\qquad p>1/4,\qquad g>3/4,\qquad pg-e^2>1/10.
\]

The stored exact rational lower endpoints, before these simplifications, have minima approximately 0.00838216325, 0.33157750294, 0.75276327441, and 0.10401388638. These decimals are display values only; the acceptance tests and the comparisons with the four simple rationals use exact interval endpoints.

The complete output files contain one record per point box. The final coverage output is:

```
G1 exact scalar diamond geometry: 3928 high cells / 8000 conventional cells.
G2 all four FCC translates preserve scalar cell labels exactly.
G3 all 48 signed coordinate permutations preserve labels after a certified integer translation.
G4 analytic Gamma cube |kappa_i| <= 3/16: all-frequency exclusion PASS.
G5 physical sampling with epsilon_max=25, p_min=10: PASS.
G6 exact dyadic cover of 0 <= z <= y <= x <= 1, x+y+z <= 3/2: PASS.
G7 interval-certified Bloch boxes: 604
G8 analytic Gamma boxes: 13
G9 exact coverage counts: {"analytic_gamma_boxes": 13, "certified_boxes": 604, "discarded_boxes": 476, "interior_nodes": 156}
G10 complete resolved unstretched Yee bulk-gap certificate: g0 >= 1/4096.
```

The final theorem follows from Sections 3--6. In particular, it does not infer a gap from a band diagram, discard gradient modes, assume a continuum-to-Yee approximation theorem, or assume that finite termination is gapped.

## 7. Provenance, corrections, and reproducibility

A floating geometry test used initially at period 20 misclassified 42 sphere-boundary cells, resulting in 3886 rather than 3928 high cells and broken FCC periodicity. Those initial data are not inputs to this certificate. The corrected exact integer geometry is used by every certified point calculation. At period 16 the analogous cell centers do not lie on the sphere surface, so this observation is not a demonstrated error in the earlier period-16 results.

The full package contains the witness-generation code, exact interval kernel and verifier, all 604 final records, the exact geometry/coverage checker, actual outputs, and the witnesses. The compact source package can regenerate witnesses and then rerun all interval checks. The compiled shared library is not trusted input: the reproduction entrypoint compiles it from the supplied C++ source with assertions enabled.

Initial point checks were performed for the smaller frequency halfwidth 2^-18. Their verified center constants were then reused in an exact scalar interval check at halfwidth 2^-12; this does not reuse an unverified spectral assertion. The distributed reproduction script checks 2^-12 directly from freshly verified center data. Independent full point-verifier passes were run before and after overflow-check hardening; the completed logs and strengthened scalar records are included.

This is a fixed finite certificate, independent of the size of any future reduction input. It discharges L1 for one explicit resolved, scalar, unstretched crystal. It does not discharge the defect and coupling hypotheses.

## 8. Immediate quantitative input for fixed-spacing wires

The certified background supplies the upper decay needed to separate unrelated structures, without a lower-versus-upper decay-rate hypothesis. The unstretched electric matrix H=C*C-D/64 has stencil radius at most two in the cell-anchor l1 metric. Its absolute row and column sums are at most 16: each curl row and column has four unit entries, giving the bound 16 for C*C, and subtracting D/64 decreases its positive diagonal 4. Thus put J=16, g_0=1/4096 and

\[
\mu_b=\tfrac12\log(1+1/262144).
\]

For coordinate sets X,Y and |u|<=g_0/4,

\[
\boxed{\|P_X(H-uI)^{-1}P_Y^*\|\le8192
\exp[-\mu_b\operatorname{dist}_1(X,Y)].}
\]

Proof: if a=dist_1(X,Y), take f(i)=min(dist_1(i,Y),a) and W_ii=exp(mu_b f(i)). Each nonzero entry connects indices at distance at most two. Hence the row and column sums of WHW^-1-H are at most J(exp(2mu_b)-1)=g_0/4, so its operator norm has that bound. The unweighted shifted inverse has norm at most 4/(3g_0). The inverse geometric-series bound gives ||(W(H-uI)W^-1)^-1||<=2/g_0. Removing the weights on X and Y gives the claim.

In particular, for any fixed defect support of anchor diameter d_s and any straight chain with centers 20 cells apart, compressed background interactions have a bound C rho^{|a-b|}, with C=8192 exp(mu_b d_s) and rho=exp(-20mu_b)<1. Truncating the chain interaction matrix at range w gives operator-norm error at most

\[
\frac{2C\rho^{w+1}}{1-\rho},
\]

by summing the two geometric row tails. Consequently w=O(log(m/delta)) gives inverse-polynomial error uniformly in chain length. The constants are conservative but fixed. This establishes a controlled banded truncation, not an exact nearest-neighbor model and not a proof of wire transmission or endpoint conditioning. Those physical wire certificates remain to be established. No assertion r^2<a is used in this consequence.
