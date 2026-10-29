import Maxwell.Continuum.WellGevrey
import Maxwell.Continuum.EffectiveMassWell
import Maxwell.Continuum.PeriodicMaterialTranslation

/-! Actual first derivative and translation bounds for the broad well
multiplier, including its flat extension across the boundary. -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory

namespace Well

theorem qw_fderiv_norm_le (x : Space) : ‖fderiv ℝ qw x‖ ≤ 400 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
  intro v hv
  have h := qw_directional_gevrey x v hv.le 1
  simpa only [directionalDerivative, iteratedFDeriv_one_apply, Real.norm_eq_abs,
    pow_one, Nat.factorial_one, Nat.cast_one, one_pow, mul_one] using h

theorem qw_lipschitz : LipschitzWith 400 qw := by
  apply lipschitzWith_of_nnnorm_fderiv_le (qw_contDiff.differentiable (by simp))
  intro x
  exact qw_fderiv_norm_le x

theorem qw_dilated_translation_bound (h : ℝ) (a x : Space) :
    |qw (h • (x + a)) - qw (h • x)| ≤ (400 * |h|) * ‖a‖ := by
  have hb := qw_lipschitz.norm_sub_le (h • (x + a)) (h • x)
  simp only [NNReal.coe_ofNat, Real.norm_eq_abs] at hb
  rw [← smul_sub, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hb
  simpa only [mul_assoc] using hb

end Well

namespace EffectiveMass

open Bloch

def QhTranslationCommutator (h : ℝ) (a : Space) : FieldL2 →L[ℂ] FieldL2 :=
  translationOperator a * Qh h - Qh h * translationOperator a

theorem QhTranslationCommutator_ae (h : ℝ) (a : Space) (f : FieldL2) (j : Fin 3) :
    QhTranslationCommutator h a f j =ᵐ[volume] (fun x =>
      ((Well.qw (h • (x + a)) - Well.qw (h • x) : ℝ) : ℂ) * f j (x + a)) := by
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (Qh_ae h f j)
  filter_upwards [fieldTranslation_ae a (Qh h f) j, Qh_ae h (fieldTranslation a f) j,
    fieldTranslation_ae a f j, Lp.coeFn_sub (fieldTranslation a (Qh h f) j)
      (Qh h (fieldTranslation a f) j), hp] with x ht hm hf hs hp
  change (fieldTranslation a (Qh h f) j - Qh h (fieldTranslation a f) j) x = _
  dsimp only [Function.comp_apply] at hp
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ht, hp, hm, hf, Complex.ofReal_sub, sub_mul]

theorem QhTranslationCommutator_component_norm (h : ℝ) (a : Space) (f : FieldL2) (j : Fin 3) :
    ‖QhTranslationCommutator h a f j‖ ≤ (400 * |h| * ‖a‖) * ‖f j‖ := by
  rw [← (translation a).norm_map (f j)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [QhTranslationCommutator_ae h a f j, translation_ae a (f j)] with x hc ht
  rw [hc, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (Well.qw_dilated_translation_bound h a x) (norm_nonneg _)

theorem QhTranslationCommutator_norm_le (h : ℝ) (a : Space) :
    ‖QhTranslationCommutator h a‖ ≤ 400 * |h| * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (QhTranslationCommutator_component_norm h a f j)

end EffectiveMass
end Maxwell.Continuum
