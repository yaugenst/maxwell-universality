import Maxwell.Continuum.CalibrationCentralRounding
import Maxwell.Continuum.CalibrationCentral

/-! Actual central calibration blocks with rationally replaceable pi
and total energy, as bounded operators on the same full alias space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber

local instance (ν : Alias) : Decidable (IsCentralAlias ν) :=
  inferInstanceAs (Decidable (∀ j, ν j = -1 ∨ ν j = 0))

def scaledCentralFreeBlock (t E : ℝ) (r : Fin 3 → ℝ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then block (realMomentum (fun j => t*gridDirection r ν j)) E else 0

theorem scaledCentralFreeBlock_norm (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (ν : Alias) :
    ‖scaledCentralFreeBlock t E r ν‖ ≤ 40 := by
  unfold scaledCentralFreeBlock
  split_ifs with hν
  · exact block_real_scale_norm t E _ ⟨by linarith, ht.2⟩ ⟨by linarith, hE.2⟩
      (gridDirection_central r hr ν hν)
  · simp only [norm_zero]
    norm_num

def scaledCentralFree (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (scaledCentralFreeBlock t E r) (by norm_num) (scaledCentralFreeBlock_norm t E r hr ht hE)

theorem scaledCentralFree_central (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (v : FiberSpace) :
    centralAliasProjection (scaledCentralFree t E r hr ht hE v) = scaledCentralFree t E r hr ht hE v := by
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  by_cases hν : IsCentralAlias ν
  · simp only [hν, ↓reduceIte]
  · simp only [hν, ↓reduceIte]
    change 0 = scaledCentralFreeBlock t E r ν (v ν)
    rw [scaledCentralFreeBlock, ite_eq_right hν]
    rfl

theorem scaledCentralFreeBlock_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4) (ν : Alias) :
    ‖scaledCentralFreeBlock t E r ν-scaledCentralFreeBlock u F r ν‖ ≤ 16*|t-u|+|E-F| := by
  unfold scaledCentralFreeBlock
  split_ifs with hν
  · exact block_real_scale_rounding t u E F _ ht hu (gridDirection_central r hr ν hν)
  · simp only [sub_self, norm_zero]
    positivity

theorem scaledCentralFree_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) :
    ‖scaledCentralFree t E r hr ht hE-scaledCentralFree u F r hr hu hF‖ ≤ 16*|t-u|+|E-F| := by
  let C := 16*|t-u|+|E-F|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB := scaledCentralFreeBlock_rounding t u E F r hr ht hu
  have heq : scaledCentralFree t E r hr ht hE-scaledCentralFree u F r hr hu hF =
      boundedBlocks (fun ν => scaledCentralFreeBlock t E r ν-scaledCentralFreeBlock u F r ν) hC hB := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    rfl
  rw [heq]
  exact boundedBlocks_norm_le _ _ _

theorem scaledCentralFree_eq_calibration (t : Momentum) (e : ℂ) (E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E) :
    scaledCentralFree Real.pi E r hr ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩ hE = centralFree t e := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext ν
  change scaledCentralFreeBlock Real.pi E r ν (v ν) = centralFreeBlock t e ν (v ν)
  unfold scaledCentralFreeBlock centralFreeBlock
  rw [hq, henergy, aliasMomentum_grid]
  split_ifs <;> rfl

#print axioms scaledCentralFree_rounding
#print axioms scaledCentralFree_eq_calibration

end Maxwell.Continuum.Calibration
