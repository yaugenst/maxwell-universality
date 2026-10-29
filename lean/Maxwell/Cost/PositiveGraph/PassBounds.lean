import Maxwell.Cost.PositiveGraph.Pass
import Maxwell.Cost.PositiveGraph.Metadata.ArrayBounds

namespace Maxwell.Cost.PositiveGraph

/-- The charged graph pass has a quadratic word-width factor at the actual
packed array bases constructed by the metadata program. -/
theorem bitBudget_packed_le (W d K : ℕ) (hd : d < 2^W) (hk : K ≤ 3*d) :
    bitBudget W d K (4*K*(W+3)+2*(2*d+K)+2*(4*K)) ≤ 5*W+23 := by
  have hK : K < 2^(W+3) := by
    rw [pow_add]
    norm_num
    omega
  have hb := (Metadata.array_bounds W d K hd hK).diagonalBase
  have hi : (4*K+1).bits.length ≤ W+4 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    omega
  have hv : (2*d+K+1).bits.length ≤ W+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    omega
  dsimp [bitBudget,Metadata.arrayBudget] at *
  omega

theorem Pass.price_packed_le (W d K : ℕ) (hd : d < 2^W) (hk : K ≤ 3*d) :
    Pass.price W d K (4*K*(W+3)+2*(2*d+K)+2*(4*K)) ≤
      375000000*(K+1)*(W+1)^2 := by
  have hb := bitBudget_packed_le W d K hd hk
  have hwidth : bitBudget W d K (4*K*(W+3)+2*(2*d+K)+2*(4*K))+2 ≤ 25*(W+1) := by omega
  unfold Pass.price
  calc
    _ ≤ 600000*(K+1)*(25*(W+1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2)
    _ = 375000000*(K+1)*(W+1)^2 := by ring

end Maxwell.Cost.PositiveGraph
