import Maxwell.Continuum.EffectiveMassAngularInverse
import Maxwell.Continuum.EffectiveMassDiagonal
import Maxwell.Continuum.EffectiveMassGramHilbert

/-! The actual inverse angular Fourier integral of the cutoff band-vector
multiplier. Its bounded wave and compact momentum support justify the
subsequent Gram-form Fubini identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Auxiliary

theorem vectorMultiplier_stronglyMeasurable {h z : ℝ} (D : Calibration h z) :
    StronglyMeasurable (vectorMultiplier h z) := by
  apply stronglyMeasurable_of_restrict_of_restrict_compl (aliasChart_measurable h)
  · exact (vectorMultiplier_continuousOn D).domRestrict.stronglyMeasurable
  · have he : (aliasChart h)ᶜ.domRestrict (vectorMultiplier h z) = fun _ => (0 : FiberSpace) := by
      funext p
      simp only [Set.domRestrict_apply, vectorMultiplier,
        cutoffBandMultiplier_zero_off_chart D.h_pos p.val p.property,
        Complex.ofReal_zero, zero_smul]
    rw [he]
    exact stronglyMeasurable_const

def chartAmplitude (h : ℝ) (f : ScalarL2) : Space → ℂ := (aliasChart h).indicator f

theorem chartAmplitude_stronglyMeasurable (h : ℝ) (f : ScalarL2) :
    StronglyMeasurable (chartAmplitude h f) :=
  (Lp.stronglyMeasurable f).indicator (aliasChart_measurable h)

theorem chartAmplitude_integrable (h : ℝ) (f : ScalarL2) :
    Integrable (chartAmplitude h f) := by
  exact (integrableOn_Lp_of_measure_ne_top f (by norm_num) (aliasChart_finite h)).integrable_indicator
    (aliasChart_measurable h)

theorem chartAmplitude_smul_vectorMultiplier {h z : ℝ} (hh : 0 < h) (f : ScalarL2) (p : Space) :
    chartAmplitude h f p • vectorMultiplier h z p = f p • vectorMultiplier h z p := by
  by_cases hp : p ∈ aliasChart h
  · rw [chartAmplitude, Set.indicator_of_mem hp]
  · simp only [chartAmplitude, Set.indicator_of_notMem hp, vectorMultiplier,
      cutoffBandMultiplier_zero_off_chart hh p hp, Complex.ofReal_zero, zero_smul, smul_zero]

theorem bandVectorOperator_integrable {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    Integrable (fun p => bandVectorOperator D f p) := by
  have hi : Integrable (fun p => chartAmplitude h f p • vectorMultiplier h z p) := by
    apply ((chartAmplitude_integrable h f).norm.mul_const 4).mono'
      ((chartAmplitude_stronglyMeasurable h f).smul
        (vectorMultiplier_stronglyMeasurable D)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖chartAmplitude h f p • vectorMultiplier h z p‖ ≤ ‖chartAmplitude h f p‖ * 4
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (vectorMultiplier_norm_le D p) (norm_nonneg _)
  apply hi.congr
  filter_upwards [bandVectorOperator_ae D f] with p hp
  rw [hp, chartAmplitude_smul_vectorMultiplier D.h_pos]

def diagonalWave (h z : ℝ) (x p : Space) : FiberSpace :=
  angularPhase p x • vectorMultiplier h z p

theorem diagonalWave_stronglyMeasurable {h z : ℝ} (D : Calibration h z) :
    StronglyMeasurable (fun xp : Space × Space => diagonalWave h z xp.1 xp.2) := by
  have hc : Continuous (fun xp : Space × Space => angularPhase xp.2 xp.1) := by
    unfold angularPhase
    fun_prop
  exact hc.stronglyMeasurable.smul
    ((vectorMultiplier_stronglyMeasurable D).comp_measurable measurable_snd)

theorem diagonalWave_norm {h z : ℝ} (D : Calibration h z) (x p : Space) :
    ‖diagonalWave h z x p‖ ≤ 4 := by
  rw [diagonalWave, norm_smul, angularPhase_norm, one_mul]
  exact vectorMultiplier_norm_le D p

theorem inverse_bandVectorOperator {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    (angularFourier FiberSpace).symm (bandVectorOperator D f) =ᵐ[volume]
      fun x => (((2 * Real.pi) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) •
        ∫ p, chartAmplitude h f p • diagonalWave h z x p := by
  filter_upwards [angularFourier_inverse_integral (bandVectorOperator D f)
    (bandVectorOperator_integrable D f)] with x hx
  rw [hx]
  congr 1
  apply integral_congr_ae
  filter_upwards [bandVectorOperator_ae D f] with p hp
  rw [hp, diagonalWave, smul_comm (chartAmplitude h f p) (angularPhase p x),
    chartAmplitude_smul_vectorMultiplier D.h_pos]

#print axioms inverse_bandVectorOperator

end Maxwell.Continuum.EffectiveMass
