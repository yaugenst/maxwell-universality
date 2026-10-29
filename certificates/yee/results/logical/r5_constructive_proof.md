# A constructive logical reduction, independent of the supplied R5 black box

## Status and scope

This document proves the *logical* sparse-to-cubic-grid reduction needed by
the conditional physical manuscript. It does not prove any Maxwell bulk,
defect, coupling, or finite-boundary assertion. All arguments below are
analytic and exact; the companion program checks examples and construction
invariants, and is not used as evidence for an all-input assertion.

The only background facts used are elementary linear algebra, the elementary
Euler-tour algorithm, and sorting by adjacent odd-even transpositions. A
proof of the sorting bound is given below. In particular, neither a 3D graph
drawing theorem nor an external arithmetic-circuit reduction is assumed.

## 1. Exact theorem

Fix positive constants k,C and a positive constant B_in. An input consists
of a nonsingular rational n-by-n matrix M, with m=nnz(M)>=2,
condition number at most m^k, and a rational vector b. Each numerator and
denominator of M and b has at most B_in log_2(m)+B_in bits. Sparse matrix
indices use O(log m) bits. Here n<=m. Requested accuracy satisfies
m^(-C)<=eta<=1. Equivalently, we may use the smaller fixed accuracy
eta_0=m^(-ceil(C)) throughout without examining a long representation of
eta. If b=0, output x=0 and terminate.

There is a deterministic construction of a real symmetric rational matrix
Gamma supported on a subgraph of the three-dimensional unit cubic lattice,
and a rational source g_Gamma, such that:

* Gamma has maximum graph degree at most three; every nonzero off-diagonal
  entry is +1; its diagonal belongs to a fixed finite alphabet contained in
  [-3,3]; in particular ||Gamma||_2<=7.
* Its bounding rectangular box has O((m log m)^(3/2)) lattice sites, with
  constants depending only on the fixed promises. The number of unknowns
  is no larger than a fixed multiple of this volume.
* A known, effectively computable bound Kbar on ||Gamma^(-1)|| is polynomial
  in m. The matrix coefficients have constant bit length and every source
  coordinate has O(log m) bits.
* Given a solution to Gamma z=g_Gamma with relative Euclidean residual at
  most a known inverse-polynomial tolerance rho, coordinate selection and
  finite-precision rounding recover x with
  ||Mx-b||_2<=eta ||b||_2.
* Construction, writing the entire ambient occupancy array if requested,
  and decoding use O_tilde(m^(3/2)) bit operations. All graph coordinates,
  tolerances, and norm bounds have O(log m) bits.

The source depends on b through normalization and sparse coordinate
placement. The decoder performs no solve. All multiplicative constants in
this statement are independent of m and of the particular matrix.

## 2. Normalization and dyadic rounding

Write K=ceil(k), L=m^(K+1), eta_0=m^(-ceil(C)),

    a=max_ij |M_ij|,   lambda=m a,   beta=||b||_infinity,
    F=M/lambda,        g=b/beta.

Then ||F||<=1, sigma_min(F)>=1/L, and 1<=||g||<=sqrt(m).
Indeed ||M||>=a, sigma_min(M)>=a m^(-k), and
||M||<=||M||_F<=sqrt(m) a<=m a.
The desired decoded variable is x=(beta/lambda)z, where Fz=g.

Choose an integer s>=1 with

    u=2^(-s)<=eta_0/(64 m L).

Round every existing nonzero entry of F to the nearest multiple of u,
with deterministic tie-breaking; never introduce an entry outside the
original sparsity pattern. Call the rounded matrix Fhat, and delete any
zeros created by rounding. Since there are at most m changed entries,

    ||Fhat-F||<=||Fhat-F||_F<=sqrt(m)u/2<=eta_0/(64 L).

The resolvent identity, or a Neumann series applied to
I+F^(-1)(Fhat-F), gives

    ||Fhat^(-1)||<=2L.                                      (2.1)

Each |Fhat_ij| is at most one and is a dyadic with at most s fractional
digits. Here s=O_{k,C}(log m). Rational normalization and rounding use
O(m polylog(m)) bit operations and do not create common denominators
across unrelated input entries.

## 3. Bounded-fanout constant-coefficient linear circuit

Construct a directed acyclic linear circuit with the n inputs z_j.
For each nonzero dyadic coefficient, write

    |Fhat_ij| = sum_(ell=1)^s b_(ij,ell) 2^(-ell),
    b_(ij,ell) in {0,1}.

The normalization gives |Fhat_ij|<1 for m>=2. For each input z_j, create
a binary tree of copy gates, with one leaf for every nonzero bit occurrence
that uses z_j. A copy gate is w=u. If exactly one occurrence is needed,
use z_j directly. A column cannot have zero occurrences because Fhat is
nonsingular. Each input or copy output is used by at most two later gates.

Compute each coefficient times z_j by Horner gates, in decreasing ell:

    u_(s+1)=0,
    u_ell=(1/2)u_(ell+1)+(b_(ij,ell)/2)z_(j,ell).

The symbol u_(s+1)=0 is a constant, not an additional unknown. At a zero
bit the second term is absent. The leaf z_(j,ell) is distinct for each bit
occurrence. Add one sign gate v_ij=sign(Fhat_ij)u_1. Sum each row's v_ij
with a binary tree of gates w=u+v; the tree's output is o_i. For a row with
one term, o_i is that term. Nonsingularity ensures every row has a term.

Let w comprise all auxiliary gate outputs, and let S=n+dim(w).
The total number of bit occurrences is at most ms; copy trees add at most
2ms gates, Horner computations at most ms, sign gates at most m, and row
sum trees at most m. Thus

    S<=6m(s+1).                                             (3.1)

The equations consist of one defining equation per gate and the n output
equations o_i=g_i. This is a square S-by-S system H(z,w)=h, where h has g
on the output rows and zero elsewhere. Its alphabet is
{0,+1,-1,+1/2,-1/2}. Every row has at most three entries and every column
has at most three entries. The sum of absolute values in every row and
column is at most three, hence ||H||<=3. Also ||h||=||g||.

### 3.1 Polynomial stability of the circuit equations

Order gate variables topologically. Their equations are

    T w - Bz = r_aux,

where T is unit lower triangular, and B contains direct references to
the inputs. Every row of B contains at most one nonzero and each column
at most two, with magnitude at most one, so ||B||<=2. Let R select the
distinct output gates. Then ||R||<=1 and

    Fhat=R T^(-1) B.

The inverse T^(-1) is a finite weighted-path sum over the acyclic gate
graph. Each edge weight has magnitude at most one. There are at most S
paths between any two auxiliary gates. To see this, branching occurs only
in the initial copy trees. A path leaving such a tree is identified by its
exit leaf; there are at most S leaves. After leaving a copy tree it follows
a Horner chain, a sign gate, and a row summation tree, all of which have
outdegree at most one. A path ending inside a copy tree is unique.
Therefore every inverse entry has magnitude at most S and

    ||T^(-1)||<=S^2.                                       (3.2)

For an arbitrary residual r=(r_out,r_aux), elimination gives

    Fhat z = r_out - R T^(-1) r_aux

when computing H^(-1)r. By (2.1),

    ||z||<=2L(1+S^2)||r||<=4LS^2||r||,
    ||w||<=S^2(2||z||+||r||)<=9LS^4||r||.

Consequently

    ||H^(-1)||<=16 L S^4=:Q_H.                             (3.3)

For an approximate solution to H(z,w)=h, the same elimination proves

    ||Fhat z-g|| <= (1+S^2)||H(z,w)-h||.                    (3.4)

This argument bounds the inverse for arbitrary perturbations of every
circuit equation. It does not merely bound the circuit's behavior on
consistent inputs.

## 4. Symmetry and positive edges

Form

    G0 = [0 H; H^T 0],       h0=(h,0).

This is symmetric, has degree at most three, zero diagonal, and the same
norm and inverse norm as H. A solution (v,z_all) has H z_all=h and
H^T v=0, hence v=0. For an approximate solution, selecting the first
block of the residual gives the residual of H z_all=h without amplification.

For each graph edge e={i,j} of G0 of weight w_e in {+1,-1,+1/2,-1/2},
introduce a distinct mediator. Connect the mediator to its two endpoints
with +1, and give it diagonal D_ee=-1/w_e. Give endpoint i diagonal
minus the sum of its incident old weights. With E the unsigned incidence
matrix of the old graph and B this endpoint diagonal matrix, let

    Gp=[B E; E^T D].

Then D^(-1)_ee=-w_e and its Schur complement is exactly G0:

    B-E D^(-1)E^T=G0.

There are at most 3S old edges; thus the dimension U of Gp is at most 5S.
Its graph is bipartite (old vertices versus mediators), degree at most
three, and every edge is +1. Endpoint diagonals lie in the fixed set
{j/2: j=-6,-5,...,6}; mediator diagonals are in {-2,-1,1,2}.
In particular all diagonals have magnitude at most three.

Since ||D^(-1)||<=1 and ||E||<=sqrt(6), block triangular factorization gives

    ||Gp^(-1)|| <= (1+sqrt(6))^2 max(1,Q_H)
                <=16 Q_H=:Q_p.                            (4.1)

The source is (h0,0). Eliminating an approximate mediator equation gives
an old-coordinate residual at most

    (1+sqrt(6)) ||r_Gp|| < 4||r_Gp||.                      (4.2)

No variable-degree copying gadget is needed here: bounded fanout was built
into the original arithmetic circuit.

## 5. Explicit cubic-lattice routing lemma

**Lemma.** Every bipartite graph with U vertices, maximum degree at most
three, and positive unit edges can be embedded as a subdivision in a
rectangular cubic-lattice box of O(U^(3/2)) volume. Each edge is replaced
by a simple path of length at most ell_max=1024q and length congruent to
1 modulo 4, where q is a power of two with 2sqrt(U)<=q<4sqrt(U).
Paths meet only at their common graph endpoints. The construction uses
O(U^(3/2) log U) bit operations, including its explicit path output.

### 5.1 Ports, pairs, and a permutation

Let a be the least power of two with a^2>=U and put q=2a. Number graph
vertices in an a-by-a array. Give each vertex its own 2-by-2 tile in a
q-by-q port grid. Use three positions of the tile for its at most three
incidences. The fourth and all unused incidence positions are dummy ports.

Number the edges. Assign the two incidence tokens of each edge to a
distinct horizontal pair of adjacent target slots (columns 2j and 2j+1
of one row). There are q^2/2=2a^2 pairs, whereas the graph has at most
3U/2 edges. Complete the mapping of real tokens to a permutation of all
q^2 slots by assigning dummy tokens to the remaining target slots.

### 5.2 A deterministic row-column-row permutation schedule

Make a bipartite multigraph with q source-row vertices and q target-row
vertices. Each token is an edge from its initial row to its final row.
Every vertex has degree q. Because q is a power of two, decompose its
edges into q perfect matchings by recursive Euler splitting:

1. For each connected component of an even-regular bipartite multigraph,
   find an Euler circuit by the usual stack algorithm.
2. Give successive circuit edges alternating colors 0 and 1. The circuit
   length is even because the graph is bipartite. Each vertex has half
   its edges of each color, including the circuit's starting vertex.
3. Recurse on each color until degree one. Degree-one spanning subgraphs
   are perfect matchings. Their recursive color strings are numbers
   k=0,...,q-1.

Each recursion level takes O(q^2) work and there are log_2 q levels.
Give each token its matching index k. In each source row, permute tokens
so that token k is in column k. In each column, permute tokens by their
target row. In each target row, permute tokens by their target column.
The first step is a permutation because every source row has every color
once. The second is a permutation because each color matching has every
target row once. The third is a permutation because the original target
slots were a bijection.

Each line permutation uses adjacent odd-even transposition sorting with
2q parallel layers. In a layer, compare disjoint neighboring pairs of the
chosen parity, swapping an inverted pair. This bound is deliberately
looser than the standard q-layer bound.

Here is a self-contained justification of the 2q bound. By the zero-one
principle, it suffices to sort binary keys: if a comparator network fails
on ordered keys, applying a threshold between an inverted output pair
produces a binary failure, and min/max commute with thresholds. Label the
ones and zeros in their initial left-to-right orders. Each necessary
crossing is one initially inverted one-zero pair. Such a crossing is ready
once that one has crossed every initially intervening zero and that zero
has crossed every initially intervening one. At that moment the pair is
adjacent; the correct comparison parity occurs within at most two layers.
The dependency graph of these crossings is a subgraph of a rectangular
grid ordered by the one index and reverse zero index. A directed chain
contains at most (#ones)+(#zeros)-1<=q-1 crossings. Thus all crossings
finish within 2(q-1) layers, and 2q layers suffice. Stable equal keys do
not change the argument.

The three phases therefore use T=6q layers and O(q^3) comparisons. Store
the swaps as they are generated; the sorting keys have O(log U) bits.

### 5.3 Exact unit-grid swap gadget

Place each grid port (c,r) at (16c,16r,0). One sorting layer occupies a
height-16 slab. A staying token follows a vertical segment. For a swap
between (0,0,0) and (16,0,0), use these two polygonal lattice paths:

    A: (0,0,0),(0,0,4),(0,4,4),(16,4,4),
       (16,4,12),(16,0,12),(16,0,16);
    B: (16,0,0),(16,0,8),(16,-4,8),(0,-4,8),
       (0,-4,12),(0,0,12),(0,0,16).

Join consecutive listed points by all intervening unit grid edges.
Each path has length 40. Direct inspection shows that their vertices are
disjoint. Every internal point has 0<z<16, and their only points in the
slab faces are the four ports. Translate this template for every row
swap; exchange x and y for a column swap. Swap boxes in one layer are
disjoint: paired sites are disjoint, row spacing is 16, and the sideways
excursion has magnitude at most four. A staying token is at an unpaired
site and does not enter a swap box. Adjacent layers meet only at their
ports, which are occupied by a permutation of the tokens.

After T layers, continue every real incidence token vertically by 16 and
join the designated horizontal pairs at that common top height. The
pairing segments are vertex-disjoint, since distinct pairs have disjoint
columns in a row and different rows are separated by 16. Discard every
dummy token path.

### 5.4 Bottom stars and edge parities

For a graph vertex in tile (i,j), put x0=32i, y0=32j. Its three port
positions are (x0,y0,0),(x0+16,y0,0),(x0,y0+16,0).
Put the graph vertex itself at (x0,y0,z0), where z0=-16 in one bipartition
and z0=-15 in the other. Connect to port zero vertically; connect to
port one horizontally at height z0 and then vertically; do the analogous
thing for port two. These paths meet only at their graph vertex. Bottom
stars in different tiles are disjoint because each is contained in its
tile's [0,16]-by-[0,16] lower box, and tiles start 32 apart.

Each original graph edge now traces one bottom star arm, one incidence
trajectory, its top pairing, the other incidence trajectory in reverse,
and the other bottom arm. This is a simple path: all distinct incidence
trajectories are disjoint, their two bottom arms share no endpoint unless
they belong to the same graph vertex, and the original graph has no loops.
Two graph edges meet only where their bottom stars share an original vertex.

The endpoint parities differ, so every path has odd length. If a path
length is 3 modulo 4, choose one of its bottom vertical incidence arms
and replace the unit segment from z=-8 to z=-7 by a three-edge detour
one unit in the +x direction. Every incidence has a distinct vertical arm,
and these arms are 16 apart. The detour is above the horizontal bottom
spokes and below the first sorting slab, so it meets no other path. It
adds two to the length. The resulting length is 1 modulo 4.

Each incidence trajectory has length at most 40T=240q. Two bottom arms
have combined length at most 64; two top vertical extensions contribute
32, the top pairing 16, and a parity detour at most two. Thus every edge
path has length at most 480q+114<=1024q for q>=2.

All coordinates lie in a box with side lengths at most
16q+9, 16q+9, and 96q+33. Its volume is at most 100000q^3 for q>=2,
hence O(U^(3/2)). Materializing every unit path costs O(Uq), while the
permutation scheduling costs O(q^3 log U) bit operations. This proves
the routing lemma.

## 6. Unit paths preserve exact unit couplings

Apply the routing lemma to Gp. For a path of length 4j+1, put diagonal
zero on all 4j internal vertices and keep +1 on its path edges. If j=0,
retain its direct edge. Let D_wire be the block diagonal matrix on all
new internal path vertices. For the adjacency matrix T_(4j) of a path
with 4j vertices, the recurrence x_(a-1)+x_(a+1)=b_a with zero exterior
values gives

    (T_(4j)^(-1))_(1,1)=(T_(4j)^(-1))_(4j,4j)=0,
    (T_(4j)^(-1))_(1,4j)=-1,
    ||T_(4j)^(-1)||<=4j.

For completeness, the recurrence on even indices successively expresses
them as alternating sums of odd b entries from the left endpoint; the
odd indices are alternating sums of even b entries from the right
endpoint. Hence every inverse entry is 0 or +/-1, every row and column
has absolute sum at most 4j, the diagonal endpoint entries vanish, and
the far-corner entry is (-1)^(2j+1)=-1.

The path Schur complement therefore contributes exactly +1 to the
off-diagonal endpoint coupling and zero to both endpoint diagonals.
The Schur complement of all internal vertices is exactly Gp.

Let ell=1024q. Then ||D_wire^(-1)||<=ell. The terminal-to-internal
incidence block E_wire has at most three entries per row and at most
one per column, so ||E_wire||<=sqrt(3)<2. (A path with internal vertices
has at least four of them.) Block factorization gives the explicit bound

    ||Gamma^(-1)|| <= (1+2ell)^2 max(Q_p,ell)
                    <=9ell^2(Q_p+ell)=:Kbar.                (6.1)

This is O(L S^5) up to fixed constants, hence polynomial in m. The final
diagonal and degree bounds give ||Gamma||<=6, and the promised bound
seven is convenient. The source appends zeros on internal path vertices.

If an approximate solution has residual r_Gamma, its terminal values
have Gp residual at most

    (1+2ell)||r_Gamma||.                                  (6.2)

This follows directly by subtracting E_wire D_wire^(-1) times the
internal residual from the terminal residual. It is an operator-norm
bound, not an entrywise error accumulation.

## 7. Full residual and finite-precision decoding budget

Combine (6.2), (4.2), symmetry, and (3.4). With

    T_res=4(1+2ell)(1+S^2),
    rho=eta_0/(16 T_res),

a relative residual rho for Gamma produces selected circuit-input values
z with

    ||Fhat z-g||<=eta_0 ||g||/16.

Equation (2.1) implies ||z||<=3L||g||. Therefore

    ||Fz-g|| <= eta_0||g||/16
                 + (eta_0/(64L)) 3L||g||
              = 7eta_0||g||/64.

Round each selected z coordinate to a multiple of eta_0/(16m), producing
z_round. Its Euclidean rounding error is at most eta_0/(16sqrt(m)) and
in particular at most eta_0/16. Since ||F||<=1 and ||g||>=1,

    ||Fz_round-g|| < eta_0 ||g||/4.

Output the exact rational vector

    x=(beta/lambda) z_round.

Then ||Mx-b||/||b||=||Fz_round-g||/||g||<eta_0/4<=eta.
The extra margin permits harmless additional rounding if a fully dyadic
output is wanted. No inverse or global solve is evaluated by the decoder.
The selected coordinates have magnitude at most 3L sqrt(m), so the rounded
values and rational output scaling have O_{k,C,B_in}(log m) bits.

Construction uses O(m polylog m) arithmetic work before routing,
O_tilde(S^(3/2)) bit operations for routing and output, and only
coordinate restriction and O(m polylog m) work for decoding. The bounding
box, every empty site in it, and every added path vertex were counted.

## 8. Relation to the supplied normal form

This directly supplies the object called Gamma in the supplied physical
manuscripts. Its diagonal alphabet is fixed; its norm is at most seven;
its explicit inverse bound Kbar is polynomial; its ambient volume is
O_tilde(m^(3/2)); its source has short rational coordinates; and its
residual transfer is explicit. Thus the old unspecified R5 black box can
be replaced by Sections 1-7 above.

This closure of R5 alone does not close H1, H2, H3, or their alternative
physical realization obligations. In particular it cannot be used to
label the complete amended Maxwell reduction proved.
