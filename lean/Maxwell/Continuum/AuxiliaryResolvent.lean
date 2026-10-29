import Maxwell.Continuum.AuxiliaryCutoffFiber

/-! The actual whole-space cutoff resolvent, conjugated by the proved
unitary Bloch transform. Its quantitative bounds are operator bounds on
physical L², not finite truncation estimates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand Bloch MeasureTheory

def cutoffData {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    FiberMultiplier.Data (H := FiberSpace) quasiMeasure (4 * (h ^ 2)⁻¹) where
  operator := cutoffFiber z σ
  measurable := cutoffFiber_measurable D hσ0 hσ
  nonneg := by positivity
  bound := cutoffFiber_norm_le D hσ0 hσ

def fiberCutoffOperator : FiberMultiplier.Data (H := FiberSpace) quasiMeasure 1 where
  operator q := (cutoff q.val : ℂ) • ContinuousLinearMap.id ℂ FiberSpace
  measurable := ((Complex.continuous_ofReal.comp
    (cutoff_continuous.comp continuous_subtype_val)).smul continuous_const).aestronglyMeasurable
  nonneg := by norm_num
  bound q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    change ‖(cutoff q.val : ℂ) • f‖ ≤ 1 * ‖f‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg q.val)]
    exact mul_le_mul_of_nonneg_right (cutoff_le_one q.val) (norm_nonneg f)

def physicalize (T : FiberL2 →L[ℂ] FiberL2) : FieldL2 →L[ℂ] FieldL2 :=
  unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp unitary.toContinuousLinearEquiv.toContinuousLinearMap)

theorem unitary_physicalize (T : FiberL2 →L[ℂ] FiberL2) (f : FieldL2) :
    unitary (physicalize T f) = T (unitary f) := unitary.apply_symm_apply _

theorem physicalize_norm_le (T : FiberL2 →L[ℂ] FiberL2) {C : ℝ}
    (hC : 0 ≤ C) (hT : ‖T‖ ≤ C) : ‖physicalize T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖unitary.symm (T (unitary f))‖ ≤ _
  rw [unitary.symm.norm_map, ← unitary.norm_map f]
  exact T.le_of_opNorm_le hT (unitary f)

theorem physicalize_sub (S T : FiberL2 →L[ℂ] FiberL2) :
    physicalize (S - T) = physicalize S - physicalize T := by
  apply ContinuousLinearMap.ext
  intro f
  exact unitary.symm.map_sub (S (unitary f)) (T (unitary f))

theorem physicalize_symmetric (T : FiberL2 →L[ℂ] FiberL2) (hT : T.IsSymmetric) :
    (physicalize T).IsSymmetric := by
  intro f g
  change inner ℂ (physicalize T f) g = inner ℂ f (physicalize T g)
  rw [← unitary_inner (physicalize T f) g, ← unitary_inner f (physicalize T g),
    unitary_physicalize, unitary_physicalize]
  exact hT _ _

def cutoffOperator : FieldL2 →L[ℂ] FieldL2 := physicalize fiberCutoffOperator.multiplier

def resolvent {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) : FieldL2 →L[ℂ] FieldL2 :=
  physicalize (cutoffData D hσ0 hσ).multiplier

theorem resolvent_ae {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2) :
    unitary (resolvent D hσ0 hσ f) =ᵐ[quasiMeasure]
      fun q => cutoffFiber z σ q (unitary f q) := by
  rw [resolvent, unitary_physicalize]
  exact (cutoffData D hσ0 hσ).multiplier_ae (unitary f)

theorem cutoffOperator_ae (f : FieldL2) :
    unitary (cutoffOperator f) =ᵐ[quasiMeasure]
      fun q => (cutoff q.val : ℂ) • unitary f q := by
  rw [cutoffOperator, unitary_physicalize]
  exact fiberCutoffOperator.multiplier_ae (unitary f)

theorem resolvent_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    ‖resolvent D hσ0 hσ‖ ≤ 4 * (h ^ 2)⁻¹ :=
  physicalize_norm_le _ (by positivity) (cutoffData D hσ0 hσ).multiplier_norm_le

theorem resolvent_selfAdjoint {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) : IsSelfAdjoint (resolvent D hσ0 hσ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (physicalize_symmetric _ ((cutoffData D hσ0 hσ).multiplier_symmetric
      (cutoffFiber_symmetric D hσ0 hσ)))

theorem resolvent_difference_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    ‖resolvent D hσ0 hσ - resolvent D le_rfl (by positivity : 0 ≤ h ^ 4 / 64)‖ ≤
      16 * σ * (h ^ 4)⁻¹ := by
  rw [resolvent, resolvent, ← physicalize_sub]
  apply physicalize_norm_le _ (by positivity)
  exact (cutoffData D hσ0 hσ).multiplier_difference_norm_le
    (cutoffData D le_rfl (by positivity)) (by positivity)
    (cutoffFiber_difference_norm_le D hσ0 hσ)

theorem resolvent_norm_le_length {L z σ : ℝ} (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹ ^ 4 / 64) :
    ‖resolvent D hσ0 hσ‖ ≤ 4 * L ^ 2 := by
  simpa only [inv_pow, inv_inv] using resolvent_norm_le D hσ0 hσ

theorem resolvent_difference_norm_le_length {L z σ : ℝ} (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹ ^ 4 / 64) :
    ‖resolvent D hσ0 hσ - resolvent D le_rfl (by positivity : 0 ≤ L⁻¹ ^ 4 / 64)‖ ≤
      16 * σ * L ^ 4 := by
  simpa only [inv_pow, inv_inv] using resolvent_difference_norm_le D hσ0 hσ

end Maxwell.Continuum.Auxiliary
