import Maxwell.Continuum.DyadicFloorRuntime

/-! Stored-word bounds for the literal signed-floor output. They bound both
unreduced numerator channels, not only their difference. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost

theorem result_raw_width (P B : ℕ) (x : Parts) (hx : x.Width B) :
    (result P x).Width (2*B+P+2) := by
  have htwo : (2^P:ℕ).bits.length=P+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
  have hp : (scaledPositive P x).bits.length≤B+P+1 := by
    exact (RationalAccumulator.bits_mul_le _ _).trans
      (by simpa only [htwo,Nat.add_assoc] using Nat.add_le_add hx.1 (le_refl (2^P:ℕ).bits.length))
  have hn : (scaledNegative P x).bits.length≤B+P+1 := by
    exact (RationalAccumulator.bits_mul_le _ _).trans
      (by simpa only [htwo,Nat.add_assoc] using Nat.add_le_add hx.2.1 (le_refl (2^P:ℕ).bits.length))
  have hm : (scaledNegative P x*x.denominator).bits.length≤2*B+P+1 :=
    (RationalAccumulator.bits_mul_le _ _).trans (by have hd := hx.2.2;omega)
  have hs : (shiftedPositive P x).bits.length≤2*B+P+2 := by
    exact (RationalAccumulator.bits_add_le _ _).trans (by omega)
  have hq : nonnegativeNumerator P x/x.denominator≤shiftedPositive P x :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  exact ⟨(RationalWords.bits_mono hq).trans hs,hn.trans (by omega),by
    simpa only [result,show (1:ℕ).bits.length=1 by decide] using (show 1≤2*B+P+2 by omega)⟩

#print axioms result_raw_width
end Maxwell.Continuum.RationalDataflow.DyadicFloor
