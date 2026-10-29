import Maxwell.Cost.PositiveGraph.Initialize
import Maxwell.Cost.PositiveGraph.Metadata.Bounds

namespace Maxwell.Cost.PositiveGraph.Metadata

/-- A common width derived from the actual compiler dimensions. -/
def arrayBudget (W : ℕ) : ℕ := 2*W+12

theorem memoryEnd_lt (W d K : ℕ) (hd : d < 2^W) (hk : K < 2^(W+3)) :
    Initialize.memoryEnd W d K < 2^arrayBudget W := by
  have hp : 1 ≤ 2^W := Nat.one_le_pow W 2 (by decide)
  have hw : W+3 ≤ 8*2^W := by
    have h : W+3 < 2^(W+3) := Nat.lt_two_pow_self
    rw [pow_add] at h
    norm_num at h
    omega
  have hK : K ≤ 8*2^W := by
    rw [pow_add] at hk
    norm_num at hk
    omega
  have hd' : d ≤ 2^W := by omega
  have hprod : 4*K*(W+3) ≤ 256*(2^W)^2 := by nlinarith [Nat.mul_le_mul hK hw]
  have hrest : 2*(2*d+K)+2*(4*K)+4*(2*d+K) ≤ 124*2^W := by omega
  have hsquare : 2^W ≤ (2^W)^2 := by nlinarith
  have hfinal : 256*(2^W)^2+124*2^W < 4096*(2^W)^2 := by nlinarith
  have heq : 2^arrayBudget W = 4096*(2^W)^2 := by
    rw [show arrayBudget W = W*2+12 by dsimp [arrayBudget]; omega, pow_add, pow_mul]
    norm_num
    ring
  rw [heq]
  dsimp [Initialize.memoryEnd]
  omega

theorem array_bounds (W d K : ℕ) (hd : d < 2^W) (hk : K < 2^(W+3)) :
    Initialize.Bounds W d K (arrayBudget W) := by
  have h := memoryEnd_lt W d K hd hk
  have bits (n : ℕ) (hn : n ≤ Initialize.memoryEnd W d K) :
      n.bits.length ≤ arrayBudget W := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (lt_of_le_of_lt hn h)
  have hw : (W+3).bits.length ≤ W+3 := by
    simpa only [WordLength.countBits_eq] using WordLength.countBits_length (W+3)
  refine ⟨by dsimp [arrayBudget]; omega, by dsimp [arrayBudget]; omega,
    by dsimp [arrayBudget]; omega,
    bits _ (by dsimp [Initialize.memoryEnd]; omega),
    bits _ (by dsimp [Initialize.memoryEnd]; omega),
    bits _ (by dsimp [Initialize.memoryEnd]; omega),
    bits _ (by dsimp [Initialize.memoryEnd]; omega),
    bits _ (by dsimp [Initialize.memoryEnd]; omega),
    lt_of_le_of_lt (by dsimp [Initialize.memoryEnd]; omega) h,
    lt_of_le_of_lt (by dsimp [Initialize.memoryEnd]; omega) h⟩

end Maxwell.Cost.PositiveGraph.Metadata
