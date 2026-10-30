import Maxwell.Continuum.PeriodicMaterialDerivative
import Maxwell.Continuum.TranslationContinuity
import Maxwell.Continuum.L2DominatedConvergence
import Maxwell.Continuum.FourierDifferenceQuotient

/-! Strong L² differentiation of the actual translated dielectric.
Uniform pointwise bounds justify the limit for arbitrary L² input. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicMaterial

open Bloch FreeFiber MeasureTheory FourierSobolev Filter
open scoped Topology

def coefficientQuotient (j : Fin 3) (t : ℝ) (x : Space) : ℝ :=
  t⁻¹ * (coefficient (x+t • coordinateDirection j)-coefficient x)

def derivativeQuotient (j : Fin 3) (t : ℝ) : FieldL2 →L[ℂ] FieldL2 :=
  (t : ℂ)⁻¹ • (translationCommutator (t • coordinateDirection j) *
    translationOperator (-(t • coordinateDirection j)))

theorem coefficientQuotient_bound (j : Fin 3) (t : ℝ) (x : Space) :
    |coefficientQuotient j t x| ≤ 28 := by
  by_cases ht : t = 0
  · simp [coefficientQuotient, ht]
  have hb := coefficient_translation_bound (t • coordinateDirection j) x
  rw [coordinate_shift_norm] at hb
  rw [coefficientQuotient, abs_mul, abs_inv]
  calc
    _ ≤ |t|⁻¹ * (28*|t|) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg t))
    _ = 28 := by field_simp [ht]

theorem coefficientQuotient_tendsto (j : Fin 3) (x : Space) :
    Tendsto (fun t : ℝ => coefficientQuotient j t x) (𝓝[≠] 0) (𝓝 (derivativeCoefficient j x)) := by
  simpa only [coefficientQuotient, zero_add, zero_smul, add_zero, smul_eq_mul] using
    (coefficient_hasDerivAt j x).tendsto_slope_zero

theorem derivativeCoefficient_bound (j : Fin 3) (x : Space) :
    |derivativeCoefficient j x| ≤ 28 :=
  le_of_tendsto (coefficientQuotient_tendsto j x).abs
    (Filter.Eventually.of_forall fun t => coefficientQuotient_bound j t x)

theorem derivativeQuotient_ae (j : Fin 3) (t : ℝ) (f : FieldL2) (k : Fin 3) :
    derivativeQuotient j t f k =ᵐ[volume]
      fun x => (coefficientQuotient j t x : ℂ) * f k x := by
  let a : Space := t • coordinateDirection j
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (fieldTranslation_ae (-a) f k)
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹
      (translationCommutator a (fieldTranslation (-a) f) k),
    translationCommutator_ae a (fieldTranslation (-a) f) k, hp] with x hs hc ht
  change ((t : ℂ)⁻¹ • (translationCommutator a (fieldTranslation (-a) f) k) : ScalarL2) x = _
  rw [hs]
  change (t : ℂ)⁻¹ * (translationCommutator a (fieldTranslation (-a) f) k x) = _
  rw [hc]
  dsimp only [Function.comp_apply] at ht
  rw [ht]
  simp only [add_neg_cancel_right, coefficientQuotient, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_sub, mul_assoc, a]

theorem derivativeQuotient_norm_le (j : Fin 3) (t : ℝ) : ‖derivativeQuotient j t‖ ≤ 28 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  have hb (k : Fin 3) : ‖derivativeQuotient j t f k‖ ≤ 28*‖f k‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [derivativeQuotient_ae j t f k] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (coefficientQuotient_bound j t x) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hb k)

theorem derivativeQuotient_component_tendsto (j : Fin 3) (f : FieldL2) (k : Fin 3) :
    Tendsto (fun t : ℝ => derivativeQuotient j t f k) (𝓝[≠] 0)
      (𝓝 (derivativeMultiplier j f k)) := by
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun x => (coefficientQuotient j t x : ℂ) * f k x) volume :=
    (Lp.aestronglyMeasurable (derivativeQuotient j t f k)).congr
      (derivativeQuotient_ae j t f k)
  have hg : AEStronglyMeasurable
      (fun x => (derivativeCoefficient j x : ℂ) * f k x) volume :=
    (Lp.aestronglyMeasurable (derivativeMultiplier j f k)).congr
      (derivativeMultiplier_ae j f k)
  have hB : Integrable (fun x => (28*‖f k x‖)^2) volume := by
    simpa only [mul_pow] using ((Lp.memLp (f k)).norm.integrable_sq).const_mul ((28:ℝ)^2)
  apply L2Convergence.tendsto_of_dominated volume
    (fun t : ℝ => derivativeQuotient j t f k) (derivativeMultiplier j f k)
    (fun t x => (coefficientQuotient j t x : ℂ) * f k x)
    (fun x => (derivativeCoefficient j x : ℂ) * f k x) (fun x => 28*‖f k x‖)
    (fun t => derivativeQuotient_ae j t f k) (derivativeMultiplier_ae j f k)
    (Filter.Eventually.of_forall hmeas) hg hB
  · exact Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (coefficientQuotient_bound j t x) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (derivativeCoefficient_bound j x) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun x =>
      ((Complex.continuous_ofReal.tendsto _).comp (coefficientQuotient_tendsto j x)).mul_const (f k x)

theorem derivativeQuotient_tendsto (j : Fin 3) (f : FieldL2) :
    Tendsto (fun t : ℝ => derivativeQuotient j t f) (𝓝[≠] 0) (𝓝 (derivativeMultiplier j f)) := by
  have hp := tendsto_pi_nhds.mpr (fun k => derivativeQuotient_component_tendsto j f k)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ScalarL2)).continuousAt.tendsto.comp hp

#print axioms derivativeQuotient_tendsto

end Maxwell.Continuum.PeriodicMaterial
