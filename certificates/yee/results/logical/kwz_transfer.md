# Rectangular Real-RAM transfer and its exact hypothesis

## Status

The linear-algebra transfer in this document is proved independently of the
physical construction. Its complexity consequence is conditional on a valid
Maxwell reduction and on the matching randomized sparse linear-equation
hypothesis. It neither proves that physical reduction nor refutes SLTH.

Primary source: Rasmus Kyng, Di Wang, Peng Zhang, *Packing LPs are Hard to
Solve Accurately, Assuming Linear Equations are Hard*, SODA 2020,
Definitions 2.2 and 3.2, and Remark 3.1:
https://people.csail.mit.edu/virgi/6.1420/papers/packingLPs.pdf

Definition 2.2 uses squared Euclidean error relative to the projected
right-hand side. Definition 3.2 specifies full-column-rank rectangular
matrices in the Real RAM model and target parameter n^(-10k). Its text does
not explicitly specify the randomized success-probability interpretation
needed below. We therefore name that interpretation separately instead of
silently attributing it to the source. Remark 3.1 discusses a finite-point
translation under additional input normalization assumptions; it is not,
by itself, a proof of the arbitrary-real normalization used here.

## 1. Input access and dimensions

Let F0 be an r0-by-n real matrix of full column rank, with m=nnz(F0)>=2
and condition number at most m^k. The vector b has r0 real coordinates.
Input is a sparse list of nonzeros and a random-access real vector b, as
in the Real RAM model. The algorithm accesses b only at row indices of
nonzero matrix entries. Empty rows of F0 contribute zero to its column
space and to its projected right-hand side. Delete them and relabel the
active rows, using sorting if necessary, in O(m log m) operations.
Write r for the active row count. Then n<=r<=m, and deleting empty rows
does not change the nonzero singular values or the desired approximation.

For a sequential finite-bit input containing arbitrary extra empty rows,
the cost of reading that representation must also be charged. No
O(m)-reading claim is made for such a different access model. The square
short-rational theorem has n<=m and therefore no such issue.

## 2. Normalize before rounding, preserving the projected source

Set

    a=max_ij |F0_ij|,       lambda=m a,
    F=F0/lambda,            p=F^T b.

Compute p with exact Real-RAM operations *before rounding either F or b*.
Then ||F||<=1 and sigma_min(F)>=m^(-k-1). Put K_int=ceil(k) and
L=m^(K_int+1). Using the integer upper bound makes every parameter
computable with basic arithmetic; no real-power primitive is needed.

If p=0, output x=0. This is exact, because for a full-column-rank matrix
F^T b=0 is equivalent to Pi_F b=0. Otherwise put

    nu=||p||_infinity>0,   q=p/nu,
    K=[ I_r F; F^T 0_n ],  c=(0,-q).

The identity block has r nonzeros and the two off-diagonal blocks have
2m, so K has at most 3m nonzeros and dimension at most 2m. Also
1<=||c||=||q||<=sqrt(n), and all entries of K and c have magnitude at most
one. No normal matrix is formed computationally.

Let z_star satisfy F^T F z_star=q. Then the exact saddle solution is
(-F z_star,z_star), and

    z_star=F^dagger b/nu,
    x_star=(nu/lambda)z_star=F0^dagger b.                    (2.1)

The scalars lambda and nu are retained as Real-RAM words and are used only
for final output rescaling. They are not encoded as short physical input
coefficients.

## 3. Saddle norm and projection-relative residual transfer

Let G=F^T F and Pi=F G^(-1)F^T. Direct multiplication gives

    K^(-1) = [ I-Pi          F G^(-1);
               G^(-1)F^T   -G^(-1) ].

The four blocks have norms at most 1,L,L,L^2, respectively. Thus

    ||K^(-1)|| <= 1+2L+L^2 <= 4L^2=:Q0,    ||K||<=2.       (3.1)

For an approximate solution (y,z), let

    r1=y+Fz,       r2=F^T y+q.

Eliminating y yields the exact identity

    F(z-z_star)=Pi r1-F G^(-1)r2.                          (3.2)

Consequently ||F(z-z_star)||<=2L||(r1,r2)||. Moreover,

    ||q||=||F^T F z_star||<=||F|| ||F z_star||
                                 <=||F z_star||.

If ||K(y,z)-c||<=eta_s ||c||, the decoded x=(nu/lambda)z obeys

    ||F0x-Pi_F0 b|| / ||Pi_F0 b||
      = ||F(z-z_star)|| / ||F z_star||
      <= 2L eta_s.                                        (3.3)

This avoids any dependence on ||b||/||Pi_F0 b||. In particular, cancellation
in p does not invalidate the transfer, because p was computed exactly
before q was normalized and rounded.

Choose

    eta_s=m^(-(6K_int+3)).

For m>=2,

    2L eta_s <= 2m^(-5K_int-2) <= m^(-5K_int)
                                      <= n^(-5K_int)<=n^(-5k).

Squaring (3.3) therefore gives Definition 2.2's target

    ||F0x-Pi_F0 b||^2 <= n^(-10k) ||Pi_F0 b||^2.            (3.4)

The slightly smaller integer-exponent tolerance is used uniformly; the
target hypothesis retains its original parameter k.

## 4. Short dyadic saddle input

Choose a dyadic unit u satisfying

    u<=eta_s/(1024 m Q0).

Round each existing nonzero entry of K to this dyadic grid, rounding the
two symmetric occurrences of an F entry identically. Round each q entry
on the same grid; zeros stay zero. Write Khat,c_hat for the result.
The dimension and nonzero counts imply

    ||Khat-K||<=2m u<=eta_s/(512Q0),
    ||c_hat-c||<=m u<=eta_s/(1024Q0)
                             <=eta_s ||c||/1024.           (4.1)

Hence

    ||Khat^(-1)||<=2Q0,       ||Khat||<=3.                  (4.2)

Suppose a solver returns w=(y,z) with

    ||Khat w-c_hat|| <= (eta_s/64)||c_hat||.

Then

    ||w|| <=2Q0(1+eta_s/64)(1+eta_s/1024)||c||
           <3Q0||c||.

Substitution into the unrounded saddle gives

    ||Kw-c||
      <= ||Khat w-c_hat||+||Khat-K|| ||w||+||c_hat-c||
      <= eta_s[(1+1/1024)/64+3/512+1/1024]||c||
      < (eta_s/16)||c||.                                  (4.3)

All nonzero coefficients and source entries now have O_k(log m) bits.
To apply a theorem whose parameters are expressed in terms of the rounded
matrix's own nonzero count, append an m-by-m identity block with zero
source. This is explicit, counted padding: the padded nonzero count m'
lies between m and 4m, the dimension is at most 3m, and

    kappa(Khat direct-sum I_m)<=6Q0=24m^(2K_int+2).

For example, the square theorem's fixed promise exponent
K'=2K_int+7 suffices since m'>=m>=2. Its requested accuracy
eta_s/64 is at least (m')^(-(6K_int+9)). Thus both the condition and
accuracy promises have the required fixed-polynomial form in m'.

This identity padding is not necessary mathematically, but it removes an
otherwise avoidable comparison between m and the rounded sparsity count.
It costs O(m) and is included in the O_tilde(m^(3/2)) construction bound.

The needed dyadic approximations of F and q can be produced in the basic
Real RAM using comparisons and bisection on [-1,1], in O(log m)
operations per entry. No unit-cost floor operation on an arbitrary real
is assumed. The precision u can be chosen using only integer-exponent
upper bounds and repeated doubling. After rounding, the reduction uses
only short rational inputs and ordinary finite-bit computations.

## 5. Finite-bit decoding and verification

The square reduction returns short rational approximations to w. The
Real-RAM decoder ignores the identity-padding coordinates and checks the
original real saddle residual using K and c, not merely their rounded
versions. Compare squared norms, so no square-root primitive is required.
This check costs O(m). A threshold eta_s||c|| is sufficient for (3.4),
and the margin in (4.3) ensures the intended good outputs pass even if a
small extra decoding budget is allocated. The final output is obtained
by n exact Real-RAM multiplications by nu/lambda.

In a finite-bit version with short original inputs, the final scaling
and residual evaluation can instead be performed with rational arithmetic
and O(log m) output precision, charging the promised input lengths. This
does not assert a bit-complexity guarantee for unrestricted real inputs;
the unrestricted-real theorem is specifically a Real-RAM theorem.

## 6. Conditional complexity and random failures

Assume the full physical reduction has been proved for every fixed
condition and accuracy exponent, with construction and decoding cost
O_tilde((m')^(3/2)), output size N=O_tilde((m')^(3/2)), output word size
B=O(log m'), inverse-polynomial tolerance, and polynomial conditioning on
its stated good event. Suppose a uniform Maxwell solver has cost

    N^theta B polylog(N,kappa(A),1/delta)

on all promised good instances. The composed Real-RAM time is then

    O_tilde(m^(3/2)+m^(3theta/2)).                          (6.1)

The construction term must not be dropped. For gamma>3/2 and
theta<2gamma/3, both exponents in (6.1) are strictly below gamma.

A randomized physical reduction needs a hypothesis forbidding randomized
solvers for the sparse lea problem with a corresponding success model.
Call this explicitly the *matching randomized SLTH*. Definition 3.2's
text does not independently settle that interpretation. A deterministic
SLTH statement alone does not yield the randomized lower bound by fiat.

Bad physical draws may be singular or poorly conditioned. Run each
physical solve with a cap equal to the proved upper bound for a good
draw; discard a timeout. For a returned vector, decode it and check the
original saddle residual as above. An accepted output always satisfies
(3.4), regardless of the physical draw's condition number. Repeat with
fresh independent construction and solver randomness. For all sufficiently
large m, the claimed physical good probability 1-1/m (and any stated
solver success probability) gives a fixed positive probability of an
accepted solve. O(log m) capped attempts amplify this to failure below
any prescribed inverse polynomial, without changing (6.1) in soft-O
notation. Handle finitely many smaller sizes directly. This argument
does not assume a good-instance runtime guarantee controls a bad draw.

Thus, *if* the physical reduction is established, (6.1) contradicts the
matching randomized SLTH for gamma>3/2 and theta<2gamma/3. It says nothing
against faster solvers on easier Maxwell subclasses or against algorithms
whose cost is N times a polynomial in kappa.

## 7. Literature check relevant to this transfer

The primary KWZ source was inspected directly. Its definition concerns
projection-relative error, not merely a residual relative to ||b||.
Its sparse discussion gives the general rectangular iteration dependence
nnz(F0) kappa(F0), and distinguishes that from the square positive-definite
sqrt(kappa) dependence.

The primary SODA 2021 paper by Richard Peng and Santosh Vempala,
*Solving Sparse Linear Systems Faster than Matrix Multiplication*,
https://epubs.siam.org/doi/10.1137/1.9781611976465.31,
gives improvements over matrix multiplication for sufficiently sparse
matrices. The primary author talk at Simons, October 9, 2025,
https://simons.berkeley.edu/talks/santosh-vempala-georgia-institute-technology-2025-10-09,
describes a 2.271 exponent for nearly linear-sparsity polynomially
conditioned inputs. That result is not a subquadratic-in-m solver for all
the sparse systems in Definition 3.2 and therefore does not directly
contradict the intended conditional lower bound. This limited check is
not a claim of an exhaustive novelty search or of a current optimal bound.
