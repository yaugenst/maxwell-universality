import Maxwell.Continuum.WellGevrey
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds

/-! Integration by parts for the literal compactly supported wells. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric
open scoped FourierTransform

def complexify (f : Space → ℝ) : Space → ℂ := fun y => (f y : ℂ)

theorem complexify_contDiff (f : Space → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (complexify f) := Complex.ofRealCLM.contDiff.comp hf

theorem complexify_hasCompactSupport (f : Space → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (complexify f) := hf.comp_left Complex.ofReal_zero

theorem iteratedFDeriv_complexify (f : Space → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (K : ℕ) (y v : Space) :
    iteratedFDeriv ℝ K (complexify f) y (fun _ => v) =
      (directionalDerivative K f y v : ℂ) := by
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left (hf.contDiffAt (x := y)) (i := K) (by simp)
  exact congrArg (fun F => F (fun _ => v)) h

theorem complexify_iteratedFDeriv_integrable (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (K : ℕ) :
    Integrable (iteratedFDeriv ℝ K (complexify f)) (volume : Measure Space) :=
  ((complexify_contDiff f hf).continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
    ((complexify_hasCompactSupport f hfc).iteratedFDeriv K)

theorem fourier_directional_norm (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (K : ℕ) (ξ v : Space) :
    ‖𝓕 (complexify (fun y => directionalDerivative K f y v)) ξ‖ =
      (2 * Real.pi * |inner ℝ ξ v|) ^ K * ‖𝓕 (complexify f) ξ‖ := by
  have hint := complexify_iteratedFDeriv_integrable f hf hfc
  have h := congrArg (fun F => F ξ (fun _ : Fin K => v))
    (Real.fourier_iteratedFDeriv (complexify_contDiff f hf) (fun n _ => hint n) (n := K) (by simp))
  rw [Real.fourier_continuousMultilinearMap_apply (hint K)] at h
  have he : (fun y => iteratedFDeriv ℝ K (complexify f) y (fun _ => v)) =
      complexify (fun y => directionalDerivative K f y v) :=
    funext (fun y => iteratedFDeriv_complexify f hf K y v)
  rw [he] at h
  rw [h]
  simp only [VectorFourier.fourierPowSMulRight_apply, neg_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul, norm_pow, norm_neg,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  change (‖(2 : ℂ)‖ * Real.pi) ^ K *
    (|inner ℝ ξ v| ^ K * ‖𝓕 (complexify f) ξ‖) = _
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  ring

theorem fourier_directional_le (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (K : ℕ) (ξ v : Space) :
    (2 * Real.pi * |inner ℝ ξ v|) ^ K * ‖𝓕 (complexify f) ξ‖ ≤
      ∫ y, |directionalDerivative K f y v| := by
  rw [← fourier_directional_norm f hf hfc K ξ v]
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
    (volume : Measure Space) (innerₗ Space) (complexify (fun y => directionalDerivative K f y v)) ξ
  simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply, complexify,
    Complex.norm_real, Real.norm_eq_abs] using h

theorem unitBall_volume_le_eight : (volume : Measure Space).real (closedBall 0 1) ≤ 8 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three]
  norm_num only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal
    (by positivity : 0 ≤ Real.pi * 4 / 3)]
  linarith [Real.pi_lt_four]

theorem integral_abs_directional_le (f : Space → ℝ)
    (hs : tsupport f ⊆ closedBall (0 : Space) 1)
    (K : ℕ) (v : Space) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y, |directionalDerivative K f y v| ≤ C) :
    (∫ y, |directionalDerivative K f y v|) ≤ 8 * C := by
  have hi : Integrable ((closedBall (0 : Space) 1).indicator (fun _ : Space => C)) volume :=
    (integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hbound : ∀ y, |directionalDerivative K f y v| ≤
      (closedBall (0 : Space) 1).indicator (fun _ : Space => C) y := by
    intro y
    by_cases hy : y ∈ closedBall (0 : Space) 1
    · rw [indicator_of_mem hy]
      exact hb y
    · rw [indicator_of_notMem hy]
      have hz : iteratedFDeriv ℝ K f y = 0 := by
        apply Function.notMem_support.mp
        intro hm
        exact hy (hs (support_iteratedFDeriv_subset K hm))
      simp only [directionalDerivative, hz, zero_apply, abs_zero, le_refl]
  calc
    (∫ y, |directionalDerivative K f y v|) ≤
        ∫ y, (closedBall (0 : Space) 1).indicator (fun _ : Space => C) y :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hi
        (Filter.Eventually.of_forall hbound)
    _ = (volume : Measure Space).real (closedBall 0 1) * C := by
      rw [integral_indicator_const C measurableSet_closedBall, smul_eq_mul]
    _ ≤ 8 * C := mul_le_mul_of_nonneg_right unitBall_volume_le_eight hC

end Maxwell.Continuum.Well
