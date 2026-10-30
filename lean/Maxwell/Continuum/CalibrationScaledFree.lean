import Maxwell.Continuum.CalibrationRationalFree
import Maxwell.Continuum.CalibrationComplementFree

/-! The complete free inverse with a variable common momentum scale.
Its literal rational matrices and operator-norm rounding bound apply
to every alias, with the central calibration identity left exact. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber

local instance (ν : Alias) : Decidable (IsCentralAlias ν) :=
  inferInstanceAs (Decidable (∀ j, ν j = -1 ∨ ν j = 0))

def scaledFreeInverseBlock (t E : ℝ) (r : Fin 3 → ℝ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 1 else inverseBlock (realMomentum (fun j => t*gridDirection r ν j)) E

theorem scaledFreeInverseBlock_norm (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8) (ν : Alias) :
    ‖scaledFreeInverseBlock t E r ν‖ ≤ 1 := by
  unfold scaledFreeInverseBlock
  split_ifs with hν
  · exact ContinuousLinearMap.norm_id_le
  · exact inverseBlock_real_scale_norm t E _ ht hE (gridDirection_noncentral r hr ν hν)

def scaledFreeInverse (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (scaledFreeInverseBlock t E r) zero_le_one (scaledFreeInverseBlock_norm t E r hr ht hE)

theorem scaledFreeInverse_norm (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8) :
    ‖scaledFreeInverse t E r hr ht hE‖ ≤ 1 := boundedBlocks_norm_le _ _ _

theorem scaledFreeInverseBlock_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) (ν : Alias) :
    ‖scaledFreeInverseBlock t E r ν-scaledFreeInverseBlock u F r ν‖ ≤ 2*|t-u|+|E-F| := by
  unfold scaledFreeInverseBlock
  split_ifs with hν
  · simp only [sub_self, norm_zero]
    positivity
  · exact inverseBlock_real_scale_rounding t u E F _ ht hu hE hF (gridDirection_noncentral r hr ν hν)

theorem scaledFreeInverse_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) :
    ‖scaledFreeInverse t E r hr ht.1 hE-scaledFreeInverse u F r hr hu.1 hF‖ ≤ 2*|t-u|+|E-F| := by
  let C := 2*|t-u|+|E-F|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB := scaledFreeInverseBlock_rounding t u E F r hr ht hu hE hF
  have heq : scaledFreeInverse t E r hr ht.1 hE-scaledFreeInverse u F r hr hu.1 hF =
      boundedBlocks (fun ν => scaledFreeInverseBlock t E r ν-scaledFreeInverseBlock u F r ν) hC hB := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    rfl
  rw [heq]
  exact boundedBlocks_norm_le _ _ _

theorem scaledFreeInverseBlock_rational (t E : ℚ) (r : Fin 3 → ℚ) (ν : Alias) :
    scaledFreeInverseBlock t E (fun j => (r j : ℝ)) ν =
      matrixCLM ((rationalFreeInverseMatrix t E r ν).map (Rat.castHom ℂ)) := by
  unfold scaledFreeInverseBlock rationalFreeInverseMatrix
  by_cases hν : IsCentralAlias ν
  · have hb := (rationalCentralCheck_true ν).mpr hν
    simp only [hν, hb, ↓reduceIte]
    have hm : (1 : Matrix (Fin 3) (Fin 3) ℚ).map (Rat.castHom ℂ) = 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero]
    rw [hm]
    apply ContinuousLinearMap.ext
    intro v
    exact (matrixCLM_one v).symm
  · have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
      (fun h => hν ((rationalCentralCheck_true ν).mp h))
    simp only [hν, hb, Bool.false_eq_true, ↓reduceIte]
    rw [rationalInverseMatrix_sound]
    unfold inverseBlock
    simp only [Complex.ofReal_ratCast]
    simp only [rationalDirection, gridDirection, Rat.cast_add, Rat.cast_intCast,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

theorem aliasMomentum_grid (r : Fin 3 → ℝ) (ν : Alias) :
    aliasMomentum (realMomentum (fun j => Real.pi*r j)) ν =
      realMomentum (fun j => Real.pi*gridDirection r ν j) := by
  rw [aliasMomentum_real]
  congr 1
  funext j
  unfold gridDirection
  ring

theorem scaledFreeInverse_eq_calibration (t : Momentum) (e : ℂ) (E : ℝ) (r : Fin 3 → ℝ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E) :
    scaledFreeInverse Real.pi E r hr Real.pi_gt_three.le hE = (calibrationFreeInverse t e ht he).map := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext ν
  change scaledFreeInverseBlock Real.pi E r ν (v ν) = calibrationInverseBlock t e ν (v ν)
  unfold scaledFreeInverseBlock calibrationInverseBlock
  rw [hq, henergy, aliasMomentum_grid]
  split_ifs <;> rfl

#print axioms scaledFreeInverse_rounding
#print axioms scaledFreeInverseBlock_rational
#print axioms scaledFreeInverse_eq_calibration

end Maxwell.Continuum.Calibration
