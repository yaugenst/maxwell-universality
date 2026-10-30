import Maxwell.Continuum.CalibrationComplementEquations

/-! Literal central and off-diagonal material blocks for the
24-dimensional calibration Schur complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped Classical

def calibrationCentralMaterial (t : Momentum) (e : ℂ) : FiberSpace →L[ℂ] FiberSpace :=
  centralFree t e-(backgroundAmplitude : ℂ) • (centralAliasProjection*potential*centralAliasProjection)

def calibrationRightCoupling : FiberSpace →L[ℂ] FiberSpace :=
  -(backgroundAmplitude : ℂ) • (noncentralAliasProjection*potential*centralAliasProjection)

def calibrationLeftCoupling : FiberSpace →L[ℂ] FiberSpace :=
  -(backgroundAmplitude : ℂ) • (centralAliasProjection*potential*noncentralAliasProjection)

private theorem compressed_potential_norm (P Q : FiberSpace →L[ℂ] FiberSpace)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖-(backgroundAmplitude : ℂ) • (P*potential*Q)‖ ≤ 7*backgroundAmplitude := by
  have hb : ‖P*potential*Q‖ ≤ 7 := by
    calc
      _ ≤ ‖P*potential‖*‖Q‖ := norm_mul_le _ _
      _ ≤ (1*7)*1 := mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul hP potential_norm_le (norm_nonneg _) zero_le_one)) hQ (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  exact (mul_le_mul_of_nonneg_left hb backgroundAmplitude_pos.le).trans_eq (mul_comm _ _)

theorem calibrationRightCoupling_norm : ‖calibrationRightCoupling‖ ≤ 7*backgroundAmplitude :=
  compressed_potential_norm _ _ noncentralAliasProjection_norm centralAliasProjection_norm

theorem calibrationLeftCoupling_norm : ‖calibrationLeftCoupling‖ ≤ 7*backgroundAmplitude :=
  compressed_potential_norm _ _ centralAliasProjection_norm noncentralAliasProjection_norm

theorem calibrationCentralMaterial_central (t : Momentum) (e : ℂ) (u : FiberSpace) :
    centralAliasProjection (calibrationCentralMaterial t e u) = calibrationCentralMaterial t e u := by
  change centralAliasProjection (centralFree t e u - (backgroundAmplitude : ℂ) •
    centralAliasProjection (potential (centralAliasProjection u))) = _
  rw [map_sub, map_smul, centralFree_projection, centralAliasProjection_idempotent]
  rfl

theorem calibrationLeftCoupling_central (u : FiberSpace) :
    centralAliasProjection (calibrationLeftCoupling u) = calibrationLeftCoupling u := by
  change centralAliasProjection (-(backgroundAmplitude : ℂ) •
    centralAliasProjection (potential (noncentralAliasProjection u))) = _
  rw [map_smul, centralAliasProjection_idempotent]
  rfl

theorem calibrationRightCoupling_noncentral (u : FiberSpace) :
    noncentralAliasProjection (calibrationRightCoupling u) = calibrationRightCoupling u := by
  change noncentralAliasProjection (-(backgroundAmplitude : ℂ) •
    noncentralAliasProjection (potential (centralAliasProjection u))) = _
  rw [map_smul, noncentralAliasProjection_idempotent]
  rfl

theorem central_operator (t : Momentum) (e : ℂ)
    (u : (operator (scaledMomentum t) (totalEnergy e)).domain) :
    centralAliasProjection (operator (scaledMomentum t) (totalEnergy e) u) = centralFree t e u.val := by
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  change (if IsCentralAlias ν then block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) (u.val ν)
    else 0) = centralFreeBlock t e ν (u.val ν)
  unfold centralFreeBlock
  split_ifs <;> rfl

theorem material_central (t : Momentum) (e : ℂ)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) :
    centralAliasProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) =
      centralFree t e u.val-(backgroundAmplitude : ℂ) • centralAliasProjection (potential u.val) := by
  rw [materialFiber_apply, map_sub, map_smul, central_operator]

theorem material_central_input (t : Momentum) (e : ℂ) (u : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨centralAliasProjection u,centralAliasProjection_mem_domain _ _ u⟩ =
        calibrationCentralMaterial t e u+calibrationRightCoupling u := by
  rw [materialFiber_apply, ← centralFree_apply]
  change centralFree t e u-(backgroundAmplitude : ℂ) • potential (centralAliasProjection u) =
    (centralFree t e u-(backgroundAmplitude : ℂ) •
      centralAliasProjection (potential (centralAliasProjection u))) +
      -(backgroundAmplitude : ℂ) • (potential (centralAliasProjection u)-
        centralAliasProjection (potential (centralAliasProjection u)))
  simp only [smul_sub, neg_smul]
  abel

theorem material_central_complement (t : Momentum) (e : ℂ)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : centralAliasProjection u.val = 0) :
    centralAliasProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) =
      calibrationLeftCoupling u.val := by
  rw [material_central]
  have hf : centralFree t e u.val = 0 := by
    rw [← centralFree_central t e u.val, hu, map_zero]
  rw [hf, zero_sub]
  change -((backgroundAmplitude : ℂ) • centralAliasProjection (potential u.val)) =
    -(backgroundAmplitude : ℂ) • centralAliasProjection (potential (u.val-centralAliasProjection u.val))
  rw [hu, sub_zero, neg_smul]

#print axioms material_central_input
#print axioms material_central_complement

end Maxwell.Continuum.Calibration
