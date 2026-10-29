import Maxwell.Cost.ModeRead.Signed
import Maxwell.Cost.RationalCanonical.Value

namespace Maxwell.Cost.ModeRead.Signed

/-- Conversion preserves the signed channel fraction, even when its common
denominator is not the reduced denominator of that rational. -/
theorem scalar_value (p n denominator : ℕ) :
    RationalCanonical.value (decide (p<n)) ((p:ℤ)-n).natAbs denominator =
      ((p:ℚ)-n)/denominator := by
  have hs : SignedDifference.sign p.bits n.bits = decide (p<n) := by
    apply Bool.eq_iff_iff.mpr
    simp only [SignedDifference.sign_iff, RationalAccumulator.address_bits, decide_eq_true_eq]
  have h := SignedDifference.signed_value p.bits n.bits
  rw [hs, IntegerNormSquare.magnitude_eq, RationalAccumulator.address_bits,
    RationalAccumulator.address_bits] at h
  change (if decide (p<n) then -(((p:ℤ)-n).natAbs:ℤ) else (((p:ℤ)-n).natAbs:ℤ)) =
    (p:ℤ)-n at h
  have hc : (if decide (p<n) then -(((p:ℤ)-n).natAbs:ℚ) else (((p:ℤ)-n).natAbs:ℚ)) =
      (p:ℚ)-n := by
    have hh := congrArg (fun z : ℤ => (z : ℚ)) h
    simpa only [apply_ite, Int.cast_neg, Int.cast_natCast, Int.cast_sub] using hh
  exact congrArg (fun q : ℚ => q/denominator) hc

end Maxwell.Cost.ModeRead.Signed
