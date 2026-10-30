import Maxwell.Continuum.CalibrationSupercellTranslationLocal
import Maxwell.Continuum.CalibrationSupercellWell

/-! Exact alias translation of a well field equals physical translation,
with the supercell boundary excluded by the proved compact support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier MeasureTheory EffectiveMass
open Bloch (fieldTranslation fieldTranslation_neg_apply)
open scoped InnerProduct

variable (M : ℕ) [NeZero M]

theorem fiber_inner_single (n : Alias) (v : Polarization) (u : FiberSpace) :
    inner ℂ (lp.single 2 n v) u=inner ℂ v (u n) :=
  lp.inner_single_left n v u

theorem analysis_translated_Qh (hEven : Even M) {L : ℝ} (hL : 1≤L) (a : Alias)
    (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ)) (f : FieldL2) :
    (embedding M).toContinuousLinearMap.adjoint
      (fieldTranslation (latticeShift a) (Qh L⁻¹ f))=
      exactTranslation M a ((embedding M).toContinuousLinearMap.adjoint (Qh L⁻¹ f)) := by
  classical
  apply lp.ext
  funext n
  apply ext_inner_left ℂ
  intro v
  rw [exactTranslation_apply,inner_smul_right,← fiber_inner_single,
    ← fiber_inner_single]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (embedding M (lp.single 2 n v))
      (fieldTranslation (latticeShift a) (Qh L⁻¹ f))=
    exactPhase M a n*inner ℂ (embedding M (lp.single 2 n v)) (Qh L⁻¹ f)
  have ht := (fieldTranslation (latticeShift a)).inner_map_map
    (fieldTranslation (-latticeShift a) (embedding M (lp.single 2 n v))) (Qh L⁻¹ f)
  rw [fieldTranslation_neg_apply] at ht
  rw [ht]
  have hQ (x y : FieldL2) : inner ℂ (Qh L⁻¹ x) y=inner ℂ x (Qh L⁻¹ y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (Qh_selfAdjoint L⁻¹)) x y
  rw [← hQ,Qh_translated_single M hEven hL a n hM v,inner_smul_left,
    starRingEnd_apply,star_star,hQ]

theorem embedding_translated_Qh (hEven : Even M) {L : ℝ} (hL : 1≤L) (a : Alias)
    (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ)) (f : FieldL2) :
    embedding M (exactTranslation M a
      ((embedding M).toContinuousLinearMap.adjoint (Qh L⁻¹ f)))=
      fieldTranslation (latticeShift a) (Qh L⁻¹ f) := by
  rw [← analysis_translated_Qh M hEven hL a hM f]
  have hMa : 16*(L+(imageRadius (-a) : ℝ)+1)≤(M : ℝ) := by rwa [radius_neg]
  have he := embedding_range_translatedQh M hL (-a) hMa f
  have hn : latticeShift (-a)=-latticeShift a := by
    apply PiLp.ext
    intro j
    simp only [latticeShift,PiLp.smul_apply,Bloch.integerVector_apply,Pi.neg_apply,
      Int.cast_neg,PiLp.neg_apply,smul_eq_mul,mul_neg]
  simpa only [hn,neg_neg] using he

theorem embedding_translation_well (hEven : Even M) {L : ℝ} (hL : 1≤L) (a : Alias)
    (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (hs : 4≤2*(M : ℝ)/L) (u : FiberSpace) :
    embedding M (exactTranslation M a
      (aliasMultiplier (rootTorus (2*(M : ℝ)/L) hs) u))=
      fieldTranslation (latticeShift a) (Qh L⁻¹ (embedding M u)) := by
  have hM0 : 16*(L+1)≤(M : ℝ) := by
    have hr : (0 : ℝ) ≤ (imageRadius a : ℝ) := by positivity
    linarith only [hM,hr]
  have he := embedding_translated_Qh M hEven hL a hM (embedding M u)
  rw [Qh_embedding M hEven hL hM0 hs] at he
  have hi (v : FiberSpace) : (embedding M).toContinuousLinearMap.adjoint (embedding M v)=v := by
    exact embedding_adjoint_embedding M v
  rw [hi] at he
  rw [Qh_embedding M hEven hL hM0 hs]
  exact he

#print axioms embedding_translation_well

end Maxwell.Continuum.Calibration.Supercell
