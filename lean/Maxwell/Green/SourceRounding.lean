import Maxwell.Defect.WeightedModeRefinement
import Maxwell.Green.ReciprocalBitBounds

/-! Final fixed-denominator source coordinates. Coordinate rounding is
performed on computed rationals and spends a controlled part of the norm budget. -/
namespace Maxwell.Defect.SourceRounding
open scoped BigOperators
set_option maxHeartbeats 600000
variable {n : ℕ}

def coordinateBudget (n b : ℕ) : ℚ := (1/2 : ℚ)^b / (n+1)

theorem coordinateBudget_pos (n b : ℕ) : 0 < coordinateBudget n b := by
  unfold coordinateBudget
  positivity

def roundVector (q : Fin n → ℚ) (b : ℕ) : Fin n → ℚ := fun i =>
  (Realization.selectedRound (coordinateBudget n b) (coordinateBudget_pos n b) (q i)).value

theorem euclidean_norm_le_sum (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hsum : x = ∑ i, EuclideanSpace.single i (x i) := by
    ext i
    simp
  calc
    ‖x‖ = ‖∑ i, EuclideanSpace.single i (x i)‖ := congrArg norm hsum
    _ ≤ ∑ i, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem roundVector_error (q : Fin n → ℚ) (b : ℕ) :
    ‖rationalVector (roundVector q b) - rationalVector q‖ ≤ (1/2 : ℝ)^b / 2 := by
  apply (euclidean_norm_le_sum _).trans
  have hcoordinate (i : Fin n) :
      |(rationalVector (roundVector q b) - rationalVector q) i| ≤
        ((coordinateBudget n b : ℚ) : ℝ)/2 := by
    have h := Realization.selectedRound_error (coordinateBudget n b) (coordinateBudget_pos n b) (q i)
    change |((roundVector q b i : ℚ) : ℝ) - (q i : ℝ)| ≤ _
    exact_mod_cast h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoordinate i)
  apply hsum.trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    coordinateBudget, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat]
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hb : 0 ≤ (1/2 : ℝ)^b := by positivity
  have hfrac : (n : ℝ)/((n : ℝ)+1) ≤ 1 := (div_le_one hn).mpr (by linarith)
  calc
    _ = ((n : ℝ)/((n : ℝ)+1)) * ((1/2 : ℝ)^b/2) := by ring
    _ ≤ 1 * ((1/2 : ℝ)^b/2) := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = _ := one_mul _

def roundedWeightedVector (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ) (b : ℕ) : Fin n → ℚ :=
  roundVector (WeightedModeRefinement.weightedVector W q (b+1)) b

theorem roundedWeightedVector_error (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n))
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hu : ‖u‖ = 1)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b) - u‖ ≤ ((2 : ℝ)^b)⁻¹) (b : ℕ) :
    ‖rationalVector (roundedWeightedVector W q b) - sqrtWeightOperator W u‖ ≤
      (1/2 : ℝ)^b := by
  have hw := (WeightedModeRefinement.weightedVector_spec W q u hW hW1 hu hqnorm hqerror (b+1)).2
  have hr := roundVector_error (WeightedModeRefinement.weightedVector W q (b+1)) b
  have ht := norm_sub_le_norm_sub_add_norm_sub (rationalVector (roundedWeightedVector W q b))
    (rationalVector (WeightedModeRefinement.weightedVector W q (b+1))) (sqrtWeightOperator W u)
  apply ht.trans
  apply (add_le_add hr hw).trans_eq
  rw [pow_succ]
  simp only [one_div, inv_pow]
  ring

theorem coordinateBudget_bits (n b : ℕ) :
    (coordinateBudget n b).den.size ≤ 2*b + (n+1).size + 1 := by
  have hp := Maxwell.Green.pow_den_size (1/2) b
  have hd := Maxwell.Green.div_den_size ((1/2 : ℚ)^b) ((n : ℚ)+1) (by positivity)
  norm_num at hp
  have htwo : Nat.size 2 = 2 := by decide
  rw [htwo] at hp
  have hnum : ((n : ℚ)+1).num.natAbs = n+1 := by
    norm_cast
  have hden : ((1/2 : ℚ)^b).den = 2^b := by rw [Rat.den_pow]; norm_num
  rw [hnum, hden] at hd
  unfold coordinateBudget
  omega

theorem roundedWeightedVector_bits (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ)
    (u : EuclideanSpace ℝ (Fin n))
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hu : ‖u‖ = 1)
    (hqnorm : ∀ b, ‖rationalVector (q b)‖ ≤ 1)
    (hqerror : ∀ b, ‖rationalVector (q b) - u‖ ≤ ((2 : ℝ)^b)⁻¹) (b : ℕ) (i : Fin n) :
    Maxwell.rationalBitLength (roundedWeightedVector W q b i) ≤ 4*b+2*(n+1).size+5 := by
  have hw := (WeightedModeRefinement.weightedVector_spec W q u hW hW1 hu hqnorm hqerror (b+1)).1
  have hx : |WeightedModeRefinement.weightedVector W q (b+1) i| ≤ (2 : ℚ)^0 := by
    have hh := (PiLp.norm_apply_le (rationalVector (WeightedModeRefinement.weightedVector W q (b+1))) i).trans hw
    change ‖(WeightedModeRefinement.weightedVector W q (b+1) i : ℝ)‖ ≤ 1 at hh
    rw [Real.norm_eq_abs] at hh
    simpa only [pow_zero] using (Rat.cast_le (K := ℝ)).mp (by simpa only [Rat.cast_abs, Rat.cast_one] using hh)
  have hr := Realization.selectedRound_rationalBitLength (coordinateBudget n b)
    (coordinateBudget_pos n b) (WeightedModeRefinement.weightedVector W q (b+1) i) 0 hx
  have hp := Realization.precisionBits_le_den_size (coordinateBudget n b) (coordinateBudget_pos n b)
  have hd := coordinateBudget_bits n b
  change Maxwell.rationalBitLength
    (Realization.selectedRound (coordinateBudget n b) (coordinateBudget_pos n b)
      (WeightedModeRefinement.weightedVector W q (b+1) i)).value ≤ _
  omega

end Maxwell.Defect.SourceRounding
