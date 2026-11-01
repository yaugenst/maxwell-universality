import Maxwell.Logical.Routing.SortPathsThreePhase

namespace Maxwell.Logical.Routing.SortPaths

def reverseCount {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (total : ℕ) : ℕ→ℕ
  | 0 => 0
  | k+1 => reverseCount initial start total k+3*length initial start (total-(k+1))

theorem reverseCount_bound {q : ℕ} (initial : SortArrays.Keys q) (start : Port q) (total k : ℕ) :
    reverseCount initial start total k ≤ 120*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have bound := length_bound initial start (total-(k+1))
    change reverseCount initial start total k+3*length initial start (total-(k+1)) ≤ 120*(k+1)
    omega

#print axioms reverseCount_bound
end Maxwell.Logical.Routing.SortPaths
