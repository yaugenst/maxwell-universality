import Maxwell.Green.CalibrationBudgetBits
import Maxwell.Green.ReciprocalCalibration

/-! Explicit finite-word bounds for the actual emitted scalar increments. -/
namespace Maxwell.Realization

/-- The terminating rational precision search never uses more digits than
the binary denominator length of its positive requested error budget. -/
theorem precisionBits_le_den_size (budget : ℚ) (hbudget : 0 < budget) :
    precisionBits budget hbudget ≤ budget.den.size := by
  unfold precisionBits geometricSteps
  apply Nat.find_min'
  apply le_min
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact Maxwell.Green.denominatorPrecision_error budget hbudget

def scalarBitOverhead (lower reserve : ℚ) : ℕ :=
  3 * lower.den.size + reserve.den.size + 5

theorem scalarBudget_den_size (lower ζ reserve : ℚ) :
    (scalarBudget lower ζ reserve).den.size ≤ 2 * ζ.den.size + scalarBitOverhead lower reserve := by
  have houter := Maxwell.Green.min_den_size lower (min (lower ^ 2 * ζ ^ 2 / 2) (2 * reserve))
  have hinner := Maxwell.Green.min_den_size (lower ^ 2 * ζ ^ 2 / 2) (2 * reserve)
  have hl := Maxwell.Green.pow_den_size lower 2
  have hζ := Maxwell.Green.pow_den_size ζ 2
  have hm := Maxwell.Green.mul_den_size (lower ^ 2) (ζ ^ 2)
  have hd := Maxwell.Green.div_den_size (lower ^ 2 * ζ ^ 2) 2 (by norm_num)
  have hr := Maxwell.Green.mul_den_size 2 reserve
  norm_num at hd hr
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo] at hd
  unfold scalarBudget scalarBitOverhead
  omega

theorem scalarRound_precision_bound (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve) :
    precisionBits (scalarBudget lower ζ reserve)
        (scalarBudget_pos lower ζ reserve hlower hζ hreserve) ≤
      2 * ζ.den.size + scalarBitOverhead lower reserve :=
  (precisionBits_le_den_size _ _).trans (scalarBudget_den_size lower ζ reserve)

/-- This bounds the actual reduced rational serialized after scalar rounding. -/
theorem scalarRound_rationalBitLength (lower ζ reserve : ℚ)
    (hlower : 0 < lower) (hζ : 0 < ζ) (hreserve : 0 < reserve)
    (v : ℚ) (integerBits : ℕ) (hv : |v| ≤ (2 : ℚ) ^ integerBits) :
    Maxwell.rationalBitLength (scalarRound lower ζ reserve hlower hζ hreserve v).value ≤
      4 * ζ.den.size + integerBits + 2 * scalarBitOverhead lower reserve + 3 := by
  have h := selectedRound_rationalBitLength (scalarBudget lower ζ reserve)
    (scalarBudget_pos lower ζ reserve hlower hζ hreserve) v integerBits hv
  have hb := scalarRound_precision_bound lower ζ reserve hlower hζ hreserve
  unfold scalarRound
  omega

end Maxwell.Realization

namespace Maxwell.Green

theorem abs_le_pow_num_size (q : ℚ) : |q| ≤ (2 : ℚ) ^ q.num.natAbs.size := by
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  calc
    |q| = |(q.num : ℚ) / q.den| := congrArg abs (Rat.num_div_den q).symm
    _ = (q.num.natAbs : ℚ) / q.den := by
      simp only [abs_div, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℚ) ≤ q.den),
        Nat.cast_natAbs, Int.cast_abs]
    _ ≤ (q.num.natAbs : ℚ) := div_le_self (Nat.cast_nonneg _) hd
    _ ≤ (2 : ℚ) ^ q.num.natAbs.size := by exact_mod_cast (Nat.lt_size_self q.num.natAbs).le

end Maxwell.Green

namespace Maxwell.Composition.PhysicalPlatform

def reciprocalBitOverhead (P : PhysicalPlatform) : ℕ :=
  P.incrementBound.num.natAbs.size +
    2 * Realization.scalarBitOverhead P.reciprocalLower (P.incrementBound / 8) + 3

/-- The actual positive, tuned scalar has a representation bound linear in
the precision input. Every other quantity in the bound is fixed by the platform. -/
theorem roundedReciprocal_rationalBitLength (P : PhysicalPlatform)
    (ζ : ℚ) (hζ : 0 < ζ) (μhat t : ℚ)
    (hμ : |(μhat : ℝ) - P.eigenvalue| ≤ (P.eigenvalueBudget ζ : ℝ))
    (ht : |(t : ℝ)| ≤ 1 / (2 * (P.incrementBound : ℝ))) :
    Maxwell.rationalBitLength (P.roundedReciprocal ζ hζ μhat t).value ≤
      4 * ζ.den.size + P.reciprocalBitOverhead := by
  have hsmall : (P.eigenvalueBudget ζ : ℝ) ≤ 1 / (4 * (P.incrementBound : ℝ)) := by
    have h : P.eigenvalueBudget ζ ≤ 1 / (4 * P.incrementBound) := min_le_right _ _
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr h
  have hb := P.calibratedReciprocal_bounds μhat t (P.eigenvalueBudget ζ) hμ hsmall ht
  have hv : |calibratedReciprocal μhat t| ≤ (2 : ℚ) ^ P.incrementBound.num.natAbs.size := by
    have hpos := P.reciprocalLower_pos.trans_le hb.1
    rw [abs_of_pos hpos]
    apply (hb.2.trans _).trans ((le_abs_self P.incrementBound).trans
      (Green.abs_le_pow_num_size P.incrementBound))
    nlinarith [P.incrementBound_pos]
  have h := Realization.scalarRound_rationalBitLength P.reciprocalLower ζ (P.incrementBound / 8)
    P.reciprocalLower_pos hζ (div_pos P.incrementBound_pos (by norm_num))
    (calibratedReciprocal μhat t) P.incrementBound.num.natAbs.size hv
  simpa only [roundedReciprocal, reciprocalBitOverhead, Nat.add_assoc] using h

end Maxwell.Composition.PhysicalPlatform
