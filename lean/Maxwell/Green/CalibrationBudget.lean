import Maxwell.Green.PhysicalCouplingCalibration
import Mathlib.Data.Nat.Size

/-! Requested precision is obtained directly from the binary denominator
length. No search over real values enters calibration. -/
namespace Maxwell.Green

def denominatorPrecision (ε : ℚ) : ℕ := ε.den.size

theorem denominatorPrecision_error (ε : ℚ) (hε : 0 < ε) :
    (1 / 2 : ℚ) ^ denominatorPrecision ε ≤ ε := by
  have hn : (1 : ℤ) ≤ ε.num := by have := Rat.num_pos.mpr hε; omega
  have hnum : (1 : ℚ) ≤ ε.num := by exact_mod_cast hn
  have hd : (0 : ℚ) < ε.den := by exact_mod_cast ε.den_pos
  have hpow : (ε.den : ℚ) ≤ (2 : ℚ)^ε.den.size := by
    exact_mod_cast (Nat.lt_size_self ε.den).le
  calc
    _ = 1 / (2 : ℚ)^ε.den.size := by simp [denominatorPrecision]
    _ ≤ 1 / (ε.den : ℚ) := one_div_le_one_div_of_le hd hpow
    _ ≤ (ε.num : ℚ) / ε.den := div_le_div_of_nonneg_right hnum hd.le
    _ = ε := Rat.num_div_den ε

end Maxwell.Green

namespace Maxwell.Composition.PhysicalPlatform
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open scoped InnerProductSpace
set_option maxHeartbeats 600000

def couplingErrorConstant (P : PhysicalPlatform) : ℚ := 4 + 3 / P.bulkGap

theorem couplingErrorConstant_pos (P : PhysicalPlatform) : 0 < P.couplingErrorConstant := by
  unfold couplingErrorConstant
  have := P.bulkGap_pos
  positivity

def couplingPrecision (P : PhysicalPlatform) (η : ℚ) : ℕ :=
  Green.denominatorPrecision (η / P.couplingErrorConstant)

theorem couplingPrecision_error (P : PhysicalPlatform) (η : ℚ) (hη : 0 < η) :
    (P.couplingErrorConstant : ℝ) * (1 / 2 : ℝ) ^ P.couplingPrecision η ≤ η := by
  have he := Green.denominatorPrecision_error (η / P.couplingErrorConstant)
    (div_pos hη P.couplingErrorConstant_pos)
  have hm := mul_le_mul_of_nonneg_left he P.couplingErrorConstant_pos.le
  rw [mul_div_cancel₀ η P.couplingErrorConstant_pos.ne'] at hm
  have hc := (Rat.cast_le (K := ℝ)).mpr hm
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, couplingPrecision] using hc

theorem signedCoupling_requested_error (P : PhysicalPlatform)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ) (n : Site) (η : ℚ) (hη : 0 < η)
    (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision η) :
    |(P.signedCoupling a n (P.couplingPrecision η) : ℝ) -
      (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode))| ≤ η := by
  let ε : ℝ := (1/2 : ℝ)^P.couplingPrecision η
  have hε : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hgap : 0 < (P.bulkGap : ℝ) := by exact_mod_cast P.bulkGap_pos
  have he := P.signedCoupling_mode_error a n (P.couplingPrecision η) ε hε ha
  apply he.trans
  apply le_trans _ (P.couplingPrecision_error η hη)
  have hsq : (1+ε)^2 ≤ 4 := by nlinarith
  have hsum : 2+ε ≤ 3 := by linarith
  have hi : 0 ≤ 1 / (P.bulkGap : ℝ) := (one_div_pos.mpr hgap).le
  calc
    _ ≤ ε * 4 + (1 / (P.bulkGap : ℝ)) * ε * 3 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsq hε)
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg hi hε))
    _ = (P.couplingErrorConstant : ℝ) * ε := by
      simp only [couplingErrorConstant, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
      ring

/-- The same finite precision allocation enforces both the error budget
and an explicit nonzero axial output. -/
def axialBudget (P : PhysicalPlatform) (ζ : ℚ) (d : ℕ) : ℚ :=
  min (ζ^2) (P.spacing.c * P.spacing.a^d / 2)

theorem axialBudget_pos (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ) (d : ℕ) :
    0 < P.axialBudget ζ d := by
  unfold axialBudget
  exact lt_min (sq_pos_of_pos hζ)
    (div_pos (mul_pos P.spacing.c_pos (pow_pos P.spacing.a_pos d)) (by norm_num))

theorem signedCoupling_axial (P : PhysicalPlatform) (ζ : ℚ) (hζ : 0 < ζ)
    (d : ℕ) (hd : P.spacing.minimumDistance ≤ d) (j : Direction)
    (a : Fin (ScalarDefect.edges P.defect).card → ℚ)
    (ha : ‖rationalCoordinates a - P.weightedMode‖ ≤
      (1/2 : ℝ)^P.couplingPrecision (P.axialBudget ζ d)) :
    let β := P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget ζ d))
    |(β : ℝ) - (-inner ℝ P.mode
      (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
        ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode))| ≤ (ζ : ℝ)^2 ∧
    (P.spacing.c : ℝ) * (P.spacing.a : ℝ)^d / 2 ≤ |(β : ℝ)| := by
  dsimp only
  have he := P.signedCoupling_requested_error a ((d : ℤ) • P.basis.mulVec (unitSite j))
    (P.axialBudget ζ d) (P.axialBudget_pos ζ hζ d) ha
  have hsmall : (P.axialBudget ζ d : ℝ) ≤ (ζ : ℝ)^2 := by
    have hh : P.axialBudget ζ d ≤ ζ^2 := min_le_left _ _
    simpa only [Rat.cast_pow] using (Rat.cast_le (K := ℝ)).mpr hh
  have hhalf : (P.axialBudget ζ d : ℝ) ≤ (P.spacing.c : ℝ) * (P.spacing.a : ℝ)^d / 2 := by
    have hh : P.axialBudget ζ d ≤ P.spacing.c * P.spacing.a^d / 2 := min_le_right _ _
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hh
  refine ⟨he.trans hsmall, ?_⟩
  have hg := P.green_axial d hd j
  have ht := abs_abs_sub_abs_le_abs_sub
    (P.signedCoupling a ((d : ℤ) • P.basis.mulVec (unitSite j))
      (P.couplingPrecision (P.axialBudget ζ d)) : ℝ)
    (-inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field)
      ((d : ℤ) • P.basis.mulVec (unitSite j)) P.mode))
  rw [abs_neg] at ht
  have hl := (abs_le.mp (ht.trans he)).1
  linarith

end Maxwell.Composition.PhysicalPlatform
