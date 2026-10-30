import Maxwell.Continuum.MomentumLeakageWellKernel

/-! The explicit Fourier-kernel tail of an actual translated well.
The reciprocal-frequency convention and its Jacobian are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Auxiliary

open MeasureTheory
open scoped Pointwise

theorem scaled_radial_setIntegral (F : Space → ℝ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    (∫ ξ : Space in {ξ | R ≤ ‖ξ‖}, F (a • ξ)) =
      (a^3)⁻¹ * ∫ p : Space in {p | a*R ≤ ‖p‖}, F p := by
  have hs : a • {ξ : Space | R ≤ ‖ξ‖} = {p : Space | a*R ≤ ‖p‖} := by
    ext p
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    change R ≤ ‖a⁻¹ • p‖ ↔ a*R ≤ ‖p‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    constructor
    · intro h
      have h' := mul_le_mul_of_nonneg_left h ha.le
      simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using h'
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using h'
  simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, hs, smul_eq_mul] using
    Measure.setIntegral_comp_smul_of_pos (volume : Measure Space) F {ξ : Space | R ≤ ‖ξ‖} ha

theorem rawWellFourier_tail (R : ℝ) :
    (∫ p : Space in {p | R ≤ ‖p‖}, ‖Well.rawPhysicalFourier Well.w p‖) ≤
      (2 : ℝ)^100 * Real.exp (-Real.sqrt R/512) :=
  Well.sqrt_decay_tail _ (fun _ => norm_nonneg _) rawWellFourier_decay R

theorem translatedWellKernel_tail {h : ℝ} (hh : 0 < h) (r : Space) (Δ : ℝ) :
    (∫ ξ : Space in {ξ | Δ/(2*Real.pi) ≤ ‖ξ‖}, ‖translatedWellKernel h r ξ‖) ≤
      (2 : ℝ)^100 * Real.exp (-Real.sqrt (Δ/h)/512) := by
  have hb : 0 < 2*Real.pi/h := by positivity
  have he : (2*Real.pi/h) * (Δ/(2*Real.pi)) = Δ/h := by field_simp
  have hc : (h^3)⁻¹ * ((2*Real.pi/h)^3)⁻¹ = ((2*Real.pi)^3)⁻¹ := by field_simp
  have hc1 : ((2*Real.pi)^3)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have hp : (1 : ℝ) ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_pow₀ hp
  simp_rw [translatedWellKernel_norm hh r]
  rw [integral_const_mul,
    scaled_radial_setIntegral (fun p => ‖Well.rawPhysicalFourier Well.w p‖) hb,
    he, ← mul_assoc, hc]
  calc
    _ ≤ 1 * ∫ p : Space in {p | Δ/h ≤ ‖p‖}, ‖Well.rawPhysicalFourier Well.w p‖ :=
      mul_le_mul_of_nonneg_right hc1 (integral_nonneg fun _ => norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact rawWellFourier_tail (Δ/h)

#print axioms translatedWellKernel_tail

end Maxwell.Continuum.Auxiliary
