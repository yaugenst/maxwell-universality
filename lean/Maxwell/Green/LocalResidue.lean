import Maxwell.Green.PoleCutoff
import Maxwell.Green.Saddle
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual normal-pole integral followed by the transverse saddle.
The normal localization error is obtained from the fixed smooth cutoff;
the transverse error is obtained from the pointwise Taylor data. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Real Complex
open scoped Topology

namespace LocalSaddleData

variable (D : LocalSaddleData) (ρ : ℝ)

def poleWeight (w : ℂ) : ℂ := (D.cutoff w : ℂ) * D.amplitude w

def localizedPoleKernel (T : ℝ) (w : ℂ) (u : ℝ) : ℂ :=
  D.poleWeight w * ((scaledPoleCutoff ρ u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
    ((u : ℂ) - D.phase w))

def normalPoleIntegral (T : ℝ) (w : ℂ) : ℂ :=
  ∫ u : ℝ, D.localizedPoleKernel ρ T w u

def normalPoleError (T : ℝ) (w : ℂ) : ℂ :=
  D.normalPoleIntegral ρ T w - (2 * π : ℂ) * I * D.kernel T w

/-- Compact support and the local amplitude Taylor estimate already imply
the ordinary amplitude integrability used in the residue estimate. -/
theorem poleWeight_integrable_of_compact (hs : HasCompactSupport D.cutoff) :
    Integrable D.poleWeight := by
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  have hsupport : Function.support D.poleWeight ⊆ tsupport D.cutoff := by
    intro w hw
    apply subset_tsupport D.cutoff
    intro hc
    apply hw
    simp [poleWeight, hc]
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  have hm : Measurable D.poleWeight := by
    exact D.cutoff_measurable.complex_ofReal.mul D.amplitude_measurable
  apply (integrableOn_const (μ := volume) (s := tsupport D.cutoff)
    (C := ‖D.amplitude0‖ + D.K₁ * max R 0) hs.measure_lt_top.ne).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isClosed_tsupport D.cutoff).measurableSet] with w hw
  by_cases hc : D.cutoff w = 0
  · simp only [poleWeight, hc, Complex.ofReal_zero, zero_mul, norm_zero]
    have := D.K₁_nonneg
    positivity
  · have hcut : ‖(D.cutoff w : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (D.cutoff_nonneg w)] using D.cutoff_le_one w
    have hamp : ‖D.amplitude w‖ ≤ ‖D.amplitude0‖ + D.K₁ * ‖w‖ := by
      calc
        _ ≤ ‖D.amplitude w - D.amplitude0‖ + ‖D.amplitude0‖ := norm_le_norm_sub_add _ _
        _ ≤ _ := by linarith [D.amplitude_error w hc]
    calc
      _ ≤ ‖D.amplitude w‖ := by
        rw [poleWeight, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hcut
      _ ≤ ‖D.amplitude0‖ + D.K₁ * ‖w‖ := hamp
      _ ≤ _ := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((hR w hw).trans (le_max_left _ _)) D.K₁_nonneg)

theorem normalPoleIntegral_measurable (T : ℝ) : Measurable (D.normalPoleIntegral ρ T) := by
  have hm : Measurable (Function.uncurry (D.localizedPoleKernel ρ T)) := by
    have := D.cutoff_measurable
    have := D.amplitude_measurable
    have := D.phase_measurable
    have := unitPoleCutoff_contDiff.continuous.measurable
    unfold Function.uncurry localizedPoleKernel poleWeight scaledPoleCutoff
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem normalPoleError_measurable (T : ℝ) : Measurable (D.normalPoleError ρ T) := by
  have hm : Measurable (D.kernel T) := by
    have := D.cutoff_measurable
    have := D.amplitude_measurable
    have := D.phase_measurable
    unfold kernel
    fun_prop
  exact (D.normalPoleIntegral_measurable ρ T).sub (hm.const_mul ((2 * π : ℂ) * I))

/-- Off the null transverse origin, quadratic positivity places every pole
on the upper side of the real normal integration line. -/
theorem phase_im_pos {w : ℂ} (hw : w ≠ 0) (hc : D.cutoff w ≠ 0) :
    0 < (D.phase w).im :=
  (mul_pos D.c_pos (sq_pos_of_pos (norm_pos_iff.mpr hw))).trans_le (D.phase_im w hc)

theorem normalPoleError_bound {C T : ℝ}
    (hC : ∀ p : ℂ, 0 < p.im → ‖p‖ ≤ ρ / 2 →
      ‖(∫ u : ℝ, (scaledPoleCutoff ρ u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
          ((u : ℂ) - p)) - (2 * π : ℂ) * I * Complex.exp (I * (T : ℂ) * p)‖ ≤ C / T ^ 2)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2) :
    ∀ᵐ w : ℂ, ‖D.normalPoleError ρ T w‖ ≤ ‖D.poleWeight w‖ * (C / T ^ 2) := by
  filter_upwards [volume.ae_ne (0 : ℂ)] with w hw
  have he : D.normalPoleError ρ T w = D.poleWeight w *
      ((∫ u : ℝ, (scaledPoleCutoff ρ u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
        ((u : ℂ) - D.phase w)) -
        (2 * π : ℂ) * I * Complex.exp (I * (T : ℂ) * D.phase w)) := by
    unfold normalPoleError normalPoleIntegral localizedPoleKernel
    rw [integral_const_mul]
    unfold poleWeight kernel
    ring
  rw [he, norm_mul]
  by_cases hc : D.cutoff w = 0
  · simp only [poleWeight, hc, Complex.ofReal_zero, zero_mul, norm_zero]
    rfl
  · exact mul_le_mul_of_nonneg_left (hC (D.phase w) (D.phase_im_pos hw hc) (hp w hc))
      (norm_nonneg _)

/-- The normal localization step contributes a uniform integrable error of
order `T⁻²`. Only ordinary amplitude integrability is required. -/
theorem exists_normalPole_error_bound (hρ : 0 < ρ) (hw : Integrable D.poleWeight)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 0 < T →
      Integrable (D.normalPoleError ρ T) ∧ Integrable (D.normalPoleIntegral ρ T) ∧
      ‖(∫ w : ℂ, D.normalPoleIntegral ρ T w) -
        (2 * π : ℂ) * I * (∫ w : ℂ, D.kernel T w)‖ ≤ A / T ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_scaledPoleCutoff_bound hρ
  refine ⟨C * ∫ w : ℂ, ‖D.poleWeight w‖,
    mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro T hT
  have hb := D.normalPoleError_bound ρ (fun p hp hp' => hbound p hp hp' T hT) hp
  have hmajor : Integrable (fun w : ℂ => ‖D.poleWeight w‖ * (C / T ^ 2)) :=
    hw.norm.mul_const _
  have he : Integrable (D.normalPoleError ρ T) :=
    hmajor.mono' (D.normalPoleError_measurable ρ T).aestronglyMeasurable hb
  have hk : Integrable (fun w : ℂ => (2 * π : ℂ) * I * D.kernel T w) :=
    (D.kernel_integrable T hT).const_mul _
  have hi : Integrable (D.normalPoleIntegral ρ T) := by
    have h := he.add hk
    exact h.congr (Filter.Eventually.of_forall (fun w => by simp [normalPoleError]))
  refine ⟨he, hi, ?_⟩
  have hI : (∫ w : ℂ, D.normalPoleIntegral ρ T w) -
      (2 * π : ℂ) * I * (∫ w : ℂ, D.kernel T w) = ∫ w : ℂ, D.normalPoleError ρ T w := by
    unfold normalPoleError
    rw [integral_sub hi hk, integral_const_mul]
  rw [hI]
  calc
    _ ≤ ∫ w : ℂ, ‖D.normalPoleError ρ T w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ, ‖D.poleWeight w‖ * (C / T ^ 2) := integral_mono_ae he.norm hmajor hb
    _ = _ := by rw [integral_mul_const]; ring

end LocalSaddleData

/-- The iterated localized three-dimensional pole integral has the exact
normal-residue times transverse-determinant coefficient. Both remainder
estimates are proved from cutoff and local Taylor data. -/
theorem localized_pole_transverse_saddle (D : LocalSaddleData) {ρ : ℝ} (hρ : 0 < ρ)
    (hw : Integrable D.poleWeight)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop,
      ‖(∫ w : ℂ, ∫ u : ℝ, D.localizedPoleKernel ρ T w u) -
        (2 * π : ℂ) * I * (D.amplitude0 *
          ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ))‖ ≤
        A * T ^ (-(3 : ℝ) / 2) := by
  obtain ⟨A, hA, hnormal⟩ := D.exists_normalPole_error_bound ρ hρ hw hp
  refine ⟨A + 2 * π * |D.errorConstant + 1|, by positivity, ?_⟩
  filter_upwards [localized_transverse_saddle D hv hq₁ hq₂ hmodel,
    eventually_ge_atTop (1 : ℝ)] with T hs hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hn := (hnormal T hTpos).2.2
  have hscale : A / T ^ 2 ≤ A * T ^ (-(3 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : -(2 : ℝ) ≤ -(3 : ℝ) / 2)
    have heq : T ^ (-(2 : ℝ)) = (T ^ 2)⁻¹ := by
      rw [Real.rpow_neg hTpos.le, Real.rpow_two]
    rw [heq] at h
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h hA
  have hnorm : ‖(2 * π : ℂ) * I‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hs' : ‖((2 * π : ℂ) * I) * ((∫ w : ℂ, D.kernel T w) -
      D.amplitude0 * ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ))‖ ≤
      (2 * π * |D.errorConstant + 1|) * T ^ (-(3 : ℝ) / 2) := by
    rw [norm_mul, hnorm]
    calc
      _ ≤ 2 * π * ((D.errorConstant + 1) * T ^ (-(3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        gcongr
        exact le_abs_self _
  have heq : (∫ w : ℂ, ∫ u : ℝ, D.localizedPoleKernel ρ T w u) -
      (2 * π : ℂ) * I * (D.amplitude0 *
        ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ)) =
      ((∫ w : ℂ, D.normalPoleIntegral ρ T w) - (2 * π : ℂ) * I *
        (∫ w : ℂ, D.kernel T w)) + ((2 * π : ℂ) * I) *
      ((∫ w : ℂ, D.kernel T w) - D.amplitude0 *
        ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ)) := by
    unfold LocalSaddleData.normalPoleIntegral
    ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (hn.trans hscale) hs').trans_eq (by ring))

/-- With a compact transverse cutoff, no integrability or asymptotic-error
premise remains in the localized pole-plus-saddle theorem. -/
theorem localized_pole_transverse_saddle_of_compact (D : LocalSaddleData) {ρ : ℝ} (hρ : 0 < ρ)
    (hs : HasCompactSupport D.cutoff)
    (hp : ∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop,
      ‖(∫ w : ℂ, ∫ u : ℝ, D.localizedPoleKernel ρ T w u) -
        (2 * π : ℂ) * I * (D.amplitude0 *
          ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ))‖ ≤
        A * T ^ (-(3 : ℝ) / 2) :=
  localized_pole_transverse_saddle D hρ (D.poleWeight_integrable_of_compact hs) hp
    hv hq₁ hq₂ hmodel

end Maxwell.Green
