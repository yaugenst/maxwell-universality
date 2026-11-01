import Maxwell.Source

/-! A common size convention includes the counted finite base cases in
resource bounds for both physical realizations. -/
namespace Maxwell.Source.SparseSystem

def effectiveSize (S : SparseSystem) : ℕ := max 2 S.nnz

theorem effectiveSize_of_two_le (S : SparseSystem) (hm : 2 ≤ S.nnz) :
    S.effectiveSize = S.nnz := max_eq_right hm

end Maxwell.Source.SparseSystem
