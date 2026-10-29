import Maxwell.Continuum.SourceNumeratorCell
import Maxwell.Continuum.SourceNumeratorPhase
import Maxwell.Continuum.EffectiveMassKernelMeasurable

/-! Literal analytic source factors. There is one signed-momentum function:
the manuscript's F⁻ is sourceFactor q and F⁺ is sourceFactor (-q). -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand FiberNormalization Set Metric

attribute [local instance] Measure.Subtype.measureSpace

theorem sourceValue_ball_integrable (h : ℝ) (u : FieldL2) :
    Integrable (fun x : SourceBall h => sourceValue h u x.val) :=
  (integrableOn_iff_comap_subtypeVal measurableSet_closedBall).mp
    (fieldValue_integrableOn (sourceMode h u) h⁻¹)

theorem sourcePairing_integrable (h : ℝ) (u : FieldL2) (v : C(SourceBall h, Polarization)) :
    Integrable (fun x : SourceBall h => bilinear (v x) (sourceValue h u x.val)) := by
  have hs := sourceValue_ball_integrable h u
  apply (hs.norm.const_mul ‖v‖).mono'
  · simpa only [bilinear_apply] using v.continuous.star.aestronglyMeasurable.inner
      hs.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => (bilinear_norm_le (v x) _).trans
      (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg _))

def sourcePairingLinear (h : ℝ) (u : FieldL2) : C(SourceBall h, Polarization) →ₗ[ℂ] ℂ where
  toFun v := ∫ x : SourceBall h, bilinear (v x) (sourceValue h u x.val)
  map_add' v w := by
    simp only [ContinuousMap.add_apply, map_add, add_apply]
    exact integral_add (sourcePairing_integrable h u v) (sourcePairing_integrable h u w)
  map_smul' c v := by
    simp only [ContinuousMap.smul_apply, map_smul, smul_apply, smul_eq_mul,
      RingHom.id_apply, integral_const_mul]

def sourcePairing (h : ℝ) (u : FieldL2) : C(SourceBall h, Polarization) →L[ℂ] ℂ :=
  (sourcePairingLinear h u).mkContinuous
    (∫ x : SourceBall h, ‖sourceValue h u x.val‖) (fun v => by
      have hb := norm_integral_le_of_norm_le ((sourceValue_ball_integrable h u).norm.const_mul ‖v‖)
        (Filter.Eventually.of_forall fun x : SourceBall h =>
          (bilinear_norm_le (v x) _).trans
            (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg _)))
      rw [integral_const_mul] at hb
      exact hb.trans_eq (mul_comm _ _))

theorem sourcePairing_apply (h : ℝ) (u : FieldL2) (v : C(SourceBall h, Polarization)) :
    sourcePairing h u v = ∫ x : SourceBall h, bilinear (v x) (sourceValue h u x.val) := rfl

def sourceIntegrand (h : ℝ) (u : FieldL2) (q : Momentum) (x : Space) : ℂ :=
  spatialPhase q x * bilinear (cellEigenfunction (unscale q) x) (sourceValue h u x)

def sourceFactor (h : ℝ) (u : FieldL2) (q : Momentum) : ℂ :=
  (fourierNormalization : ℂ) * ∫ x, sourceIntegrand h u q x

theorem sourceIntegrand_supported {h : ℝ} (hh : 0 < h) (u : FieldL2) (q : Momentum) :
    ∀ᵐ x ∂(volume : Measure Space), x ∉ SourceBall h → sourceIntegrand h u q x = 0 := by
  filter_upwards [sourceValue_supported hh u] with x hx hnot
  simp only [SourceBall, mem_closedBall, dist_zero_right, not_le] at hnot
  simp only [sourceIntegrand, hx hnot.le, map_zero, mul_zero]

theorem sourceIntegrand_ball_integrable (h : ℝ) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) : IntegrableOn (sourceIntegrand h u q) (SourceBall h) := by
  apply (integrableOn_iff_comap_subtypeVal measurableSet_closedBall).mpr
  convert sourcePairing_integrable h u (sourceCellWave h q) using 1
  funext x
  rw [sourceCellWave_apply h hq, map_smul, smul_apply]
  rfl

theorem sourceIntegrand_integrable {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) : Integrable (sourceIntegrand h u q) :=
  (sourceIntegrand_ball_integrable h u hq).integrable_of_ae_notMem_eq_zero
    (sourceIntegrand_supported hh u q)

theorem sourceFactor_eq_pairing {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    sourceFactor h u q = (fourierNormalization : ℂ) * sourcePairing h u (sourceCellWave h q) := by
  rw [sourceFactor, sourcePairing_apply]
  congr 1
  have heq : (fun x : SourceBall h => bilinear (sourceCellWave h q x) (sourceValue h u x.val)) =
      fun x : SourceBall h => sourceIntegrand h u q x.val := by
    funext x
    rw [sourceCellWave_apply h hq, map_smul, smul_apply]
    rfl
  rw [heq, integral_subtype measurableSet_closedBall]
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (sourceIntegrand_supported hh u q)).symm

theorem sourceFactor_curve_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U physicalChart) :
    AnalyticOnNhd ℂ (fun z => sourceFactor h u (g z)) U := by
  have ha : AnalyticOnNhd ℂ (fun z => (fourierNormalization : ℂ) *
      sourcePairing h u (sourceCellWave h (g z))) U := by
    intro z hz
    exact analyticAt_const.mul (((sourcePairing h u).analyticAt _).comp
      (f := fun z => sourceCellWave h (g z)) (sourceCellWave_curve_analytic h hU hg hmap z hz))
  exact AnalyticOnNhd.congr hU ha (fun z hz => (sourceFactor_eq_pairing hh u (hmap hz)).symm)

theorem sourceIntegrand_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    ∀ᵐ x ∂(volume : Measure Space), ‖sourceIntegrand h u q x‖ ≤
      (32 * Real.exp (‖sourceImaginary q‖ / h)) * ‖sourceValue h u x‖ := by
  filter_upwards [sourceValue_supported hh u] with x hx
  by_cases hs : h⁻¹ ≤ ‖x‖
  · simp only [sourceIntegrand, hx hs, map_zero, mul_zero, norm_zero]
    positivity
  · have hxn : ‖x‖ ≤ h⁻¹ := (lt_of_not_ge hs).le
    rw [sourceIntegrand, norm_mul]
    calc
      _ ≤ Real.exp (‖sourceImaginary q‖ / h) * (32 * ‖sourceValue h u x‖) :=
        mul_le_mul (sourcePhase_norm_on_support hh q hxn)
          ((bilinear_norm_le _ _).trans
            (mul_le_mul_of_nonneg_right (cellEigenfunction_norm_le (unscale_mem_chart hq) x)
              (norm_nonneg _))) (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by ring

theorem sourceFactor_scaled_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    sourceScale h * ‖sourceFactor h u q‖ ≤
      96 * Real.exp (‖sourceImaginary q‖ / h) * ‖u‖ := by
  have hn := norm_integral_le_of_norm_le
    ((sourceValue_integrable hh u).norm.const_mul (32 * Real.exp (‖sourceImaginary q‖ / h)))
    (sourceIntegrand_norm_le hh u hq)
  rw [integral_const_mul] at hn
  have hb : ‖sourceFactor h u q‖ ≤
      (32 * Real.exp (‖sourceImaginary q‖ / h)) * ∫ x, ‖sourceValue h u x‖ := by
    rw [sourceFactor, norm_mul]
    exact (mul_le_mul_of_nonneg_right fourierNormalization_norm_le (norm_nonneg _)).trans
      (by simpa only [one_mul] using hn)
  calc
    _ ≤ sourceScale h * ((32 * Real.exp (‖sourceImaginary q‖ / h)) *
        ∫ x, ‖sourceValue h u x‖) := mul_le_mul_of_nonneg_left hb (sourceScale_pos hh).le
    _ = (32 * Real.exp (‖sourceImaginary q‖ / h)) *
        (sourceScale h * ∫ x, ‖sourceValue h u x‖) := by ring
    _ ≤ (32 * Real.exp (‖sourceImaginary q‖ / h)) * (3 * ‖u‖) :=
      mul_le_mul_of_nonneg_left (sourceValue_scaled_integral_norm_le hh u) (by positivity)
    _ = _ := by ring

#print axioms sourceFactor_curve_analytic
#print axioms sourceFactor_scaled_norm_le

end Maxwell.Continuum.EffectiveMass
