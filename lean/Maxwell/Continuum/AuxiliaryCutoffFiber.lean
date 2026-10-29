import Maxwell.Continuum.AuxiliaryFiberRegularity
import Maxwell.Continuum.AuxiliaryCutoff
import Maxwell.Continuum.FiberMultiplier
import Maxwell.Continuum.BlochPeriodicGraph

/-! The literal cutoff inverse on the Bloch cell, extended by zero
outside the valid chart. No inverse outside that chart is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Bloch MeasureTheory

attribute [local irreducible] fiberResolvent fiberInverse fullResolventExtension scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

def cutoffRegion : Set QuasiCell := {q | ‖quasiMomentum q‖ < 4 * smallRadius}

theorem quasiMomentum_continuous : Continuous quasiMomentum := by
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp
    ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)

theorem cutoffRegion_isOpen : IsOpen cutoffRegion :=
  isOpen_lt quasiMomentum_continuous.norm continuous_const

def cutoffFiber (z σ : ℝ) : QuasiCell → FiberMap :=
  cutoffRegion.indicator (fun q =>
    (cutoff q.val : ℂ) • fiberResolvent z σ (fun j => q.val j))

theorem cutoffFiber_eq {z σ : ℝ} {q : QuasiCell} (hq : q ∈ cutoffRegion) :
    cutoffFiber z σ q = (cutoff q.val : ℂ) • fiberResolvent z σ (fun j => q.val j) :=
  Set.indicator_of_mem hq _

theorem cutoffFiber_zero {z σ : ℝ} {q : QuasiCell} (hq : q ∉ cutoffRegion) :
    cutoffFiber z σ q = 0 := Set.indicator_of_notMem hq _

theorem cutoffFiber_measurable {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    AEStronglyMeasurable (cutoffFiber z σ) quasiMeasure := by
  apply (aestronglyMeasurable_indicator_iff cutoffRegion_isOpen.measurableSet).mpr
  apply ContinuousOn.aestronglyMeasurable _ cutoffRegion_isOpen.measurableSet
  intro q hq
  have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
    (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
  have hp : ContinuousAt (fun p : QuasiCell => fun j => p.val j) q :=
    (continuous_pi fun j => (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val).continuousAt
  have hR : ContinuousAt (fun p : QuasiCell => fiberResolvent z σ (fun j => p.val j)) q :=
    ContinuousAt.comp (f := fun p : QuasiCell => fun j => p.val j)
      (fiberResolvent_continuousAt D hσ0 hσ _ hq') hp
  exact ((Complex.continuous_ofReal.comp
    (cutoff_continuous.comp continuous_subtype_val)).continuousAt.smul hR).continuousWithinAt

theorem cutoffFiber_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) :
    ‖cutoffFiber z σ q‖ ≤ 4 * (h ^ 2)⁻¹ := by
  by_cases hq : q ∈ cutoffRegion
  · rw [cutoffFiber_eq hq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_nonneg q.val)]
    have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
    exact (mul_le_mul_of_nonneg_right (cutoff_le_one q.val) (norm_nonneg _)).trans
      (by simpa only [one_mul] using fiberResolvent_norm_le D hσ0 hσ _ hq')
  · rw [cutoffFiber_zero hq, norm_zero]
    positivity

theorem cutoffFiber_symmetric {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) :
    (cutoffFiber z σ q).IsSymmetric := by
  by_cases hq : q ∈ cutoffRegion
  · have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (fiberResolvent_selfAdjoint D hσ0 hσ _ hq')
    rw [cutoffFiber_eq hq]
    intro u v
    change inner ℂ ((cutoff q.val : ℂ) • fiberResolvent z σ _ u) v =
      inner ℂ u ((cutoff q.val : ℂ) • fiberResolvent z σ _ v)
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    exact congrArg (fun w : ℂ => (cutoff q.val : ℂ) * w) (hs u v)
  · rw [cutoffFiber_zero hq]
    intro u v
    simp

theorem cutoffFiber_difference_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) :
    ‖cutoffFiber z σ q - cutoffFiber z 0 q‖ ≤ 16 * σ * (h ^ 4)⁻¹ := by
  by_cases hq : q ∈ cutoffRegion
  · have hsub : (cutoff q.val : ℂ) • fiberResolvent z σ (fun j => q.val j) -
        (cutoff q.val : ℂ) • fiberResolvent z 0 (fun j => q.val j) =
        (cutoff q.val : ℂ) • (fiberResolvent z σ (fun j => q.val j) -
          fiberResolvent z 0 (fun j => q.val j)) := by
      apply ContinuousLinearMap.ext
      intro f
      exact (smul_sub (cutoff q.val : ℂ) _ _).symm
    rw [cutoffFiber_eq hq, cutoffFiber_eq hq, hsub, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg q.val)]
    have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
    exact (mul_le_mul_of_nonneg_right (cutoff_le_one q.val) (norm_nonneg _)).trans
      (by simpa only [one_mul] using fiberResolvent_difference_norm_le D hσ0 hσ _ hq')
  · rw [cutoffFiber_zero hq, cutoffFiber_zero hq, sub_self, norm_zero]
    positivity

theorem cutoffFiber_graph {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) (f : FiberSpace) :
    (cutoffFiber z σ q f, (cutoff q.val : ℂ) • f) ∈
      (materialFiber (quasiMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph := by
  by_cases hq : q ∈ cutoffRegion
  · have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
      (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
    rw [cutoffFiber_eq hq]
    exact (materialFiber (quasiMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph.smul_mem
      (cutoff q.val : ℂ) (fiberResolvent_graph D hσ0 hσ _ hq' f)
  · rw [cutoffFiber_zero hq, cutoff_eq_zero_outside hq]
    simp only [Complex.ofReal_zero, zero_smul, zero_apply]
    exact (materialFiber (quasiMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph.zero_mem

end Maxwell.Continuum.Auxiliary
