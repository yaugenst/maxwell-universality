import Maxwell.Certificate.DyadicKernelSchurEval

namespace Maxwell.Certificate.DyadicKernel

abbrev Rectangular (m n : Nat) := Vector (Vector Rectangle n) m

def Rectangular.entry {m n : Nat} (a : Rectangular m n) (i : Fin m) (j : Fin n) : Rectangle :=
  a[i][j]

/-- The Gram matrix divided by a positive power of two. Its entries are
computed from the supplied columns, without proposed Gram intermediates. -/
def gramRows (p r : Nat) {m n : Nat} (a : Rectangular m n) : Rows n :=
  Rows.ofEnclosure fun i j => dotRound (p+r)
    (List.ofFn fun k : Fin m => (conjugate (a.entry k i),a.entry k j))

def crossRows (p r : Nat) {m n : Nat} (a b : Rectangular m n) : Rows n :=
  Rows.ofEnclosure fun i j => dotRound (p+r)
    (List.ofFn fun k : Fin m => (conjugate (a.entry k i),b.entry k j))

def hermitianPartRows {n : Nat} (a : Rows n) : Rows n :=
  Rows.ofEnclosure fun i j => round 1 (add (a.enclosure i j) (conjugate (a.enclosure j i)))

def diagonalShift (subtract : Bool) {n : Nat} (bound : Rectangle) (a : Rows n) : Rows n :=
  Rows.ofEnclosure fun i j => add (if i=j then bound else zero)
    (if subtract then neg (a.enclosure i j) else a.enclosure i j)

def gramNormEval (p r : Nat) {m n : Nat} (boundSquared : Rectangle)
    (a : Rectangular m n) : Bool :=
  schurEvalRows p (diagonalShift true boundSquared (gramRows p r a))

def hermitianNormEval (p : Nat) {n : Nat} (bound : Rectangle) (a : Rows n) : Bool :=
  schurEvalRows p (diagonalShift false bound a) &&
    schurEvalRows p (diagonalShift true bound a)

end Maxwell.Certificate.DyadicKernel
