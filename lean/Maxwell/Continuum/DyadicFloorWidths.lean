import Maxwell.Continuum.DyadicFloorCost

/-! Input-local word bounds for signed floor, independent of other cached words. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

theorem result_width (P W : ℕ) (x : Parts) (hx : x.Width W) :
    (result P x).Width (2*W+P+3) := by
  rcases hx with ⟨hxp,hxn,hxd⟩
  have hpow : (2^P:ℕ).bits.length=P+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  have hp : (scaledPositive P x).bits.length≤W+P+1 := by
    exact (RationalAccumulator.bits_mul_le _ _).trans (by omega)
  have hn : (scaledNegative P x).bits.length≤W+P+1 := by
    exact (RationalAccumulator.bits_mul_le _ _).trans (by omega)
  have hnd : (scaledNegative P x*x.denominator).bits.length≤2*W+P+1 :=
    (RationalAccumulator.bits_mul_le _ _).trans (by omega)
  have hsum : (shiftedPositive P x).bits.length≤2*W+P+2 :=
    (RationalAccumulator.bits_add_le _ _).trans (by omega)
  have hnum : (nonnegativeNumerator P x/x.denominator).bits.length≤2*W+P+2 := by
    rw [Nat.size_eq_bits_len] at hsum ⊢
    apply (Nat.size_le_size (Nat.div_le_self _ _)).trans
    apply (Nat.size_le_size (Nat.sub_le _ _)).trans hsum
  refine ⟨hnum.trans (by omega),hn.trans (by omega),?_⟩
  change (1:ℕ).bits.length≤2*W+P+3
  simp only [show (1:ℕ).bits.length=1 by decide]
  omega

#print axioms result_width
end Maxwell.Continuum.RationalDataflow.DyadicFloor
