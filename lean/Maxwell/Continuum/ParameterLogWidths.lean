import Maxwell.Continuum.ParameterBudgetBounds
import Maxwell.Codec.Bounds

/-! Binary word widths fit the common integer logarithm. -/
namespace Maxwell.Continuum.Parameters

theorem inputBits_le_log (m : ℕ) : unsignedBitLength (2+m)≤ inputLog m := by
  rw [Codec.unsignedBitLength_eq_size]
  apply Nat.size_le.mpr
  have h:=Nat.le_pow_clog (by decide : 1<2) (m+2)
  have positive : 0<2^Nat.clog 2 (m+2):=pow_pos (by decide) _
  simp only [inputLog,pow_add,pow_one]
  omega

theorem sourceBits_le_log (m : ℕ) : m.bits.length≤ inputLog m := by
  have h:=Codec.unsignedBitLength_mono (show m≤2+m by omega)
  rw [Codec.unsignedBitLength_eq_size,←Nat.size_eq_bits_len] at h
  exact h.trans (inputBits_le_log m)

end Maxwell.Continuum.Parameters
