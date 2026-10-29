import Maxwell.Certificate.DyadicKernelRounded

/-! Deterministic Schur elimination using nested, fixed-length arrays.
Every update is materialized once; the input contains no intermediate
factorization witnesses. Analytical soundness is proved separately. -/
namespace Maxwell.Certificate.DyadicKernel

abbrev Rows (n : Nat) := Vector (Vector Rectangle n) n

def Rows.enclosure {n : Nat} (a : Rows n) : Enclosure n := fun i j => a[i][j]

def Rows.ofEnclosure {n : Nat} (a : Enclosure n) : Rows n :=
  Vector.ofFn fun i => Vector.ofFn fun j => a i j

def schurUpdateEntry (p : Nat) (aij ai0 aj0 pivot : Rectangle) : Rectangle :=
  let product := mulRound p ai0 (conjugate aj0)
  let quotient := (divRound p product pivot).getD zero
  add aij (neg quotient)

def schurUpdateRows (p : Nat) {n : Nat} (a : Rows (n+1)) : Rows n :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    schurUpdateEntry p (a.enclosure i.succ j.succ)
      (a.enclosure i.succ 0) (a.enclosure j.succ 0) (a.enclosure 0 0)

/-- The positive pivot check rejects all divisions with a denominator
interval containing zero before the next matrix is evaluated. -/
def schurEvalRows (p : Nat) : {n : Nat} → Rows n → Bool
  | 0, _ => true
  | n+1, a =>
      decide (0 < (a.enclosure 0 0).re-((a.enclosure 0 0).radius : Int)) &&
        schurEvalRows p (n := n) (schurUpdateRows p a)

def schurEval (p : Nat) {n : Nat} (a : Enclosure n) : Bool :=
  schurEvalRows p (Rows.ofEnclosure a)

end Maxwell.Certificate.DyadicKernel
