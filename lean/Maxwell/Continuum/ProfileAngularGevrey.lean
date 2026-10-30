import Maxwell.Continuum.ProfileAngularComplex
import Maxwell.Continuum.WellRealDeriv

/-! The actual endpoint-flat radial profile and its periodic angular Gevrey estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Filter Metric
open scoped Topology

def radial (t : ℝ) : ℝ := expNegInvGlue (2*(1-t))
def angular (φ : ℝ) : ℝ := expNegInvGlue (1-Real.cos φ)

theorem angular_eq_radial (φ : ℝ) : angular φ = radial ((1+Real.cos φ)/2) := by
  unfold angular radial
  congr 1
  ring

theorem radial_contDiff : ContDiff ℝ (⊤ : ℕ∞) radial := by
  unfold radial
  exact expNegInvGlue.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem radial_nonneg (t : ℝ) : 0 ≤ radial t := expNegInvGlue.nonneg _
theorem radial_le_one (t : ℝ) : radial t ≤ 1 := by
  unfold radial expNegInvGlue
  split_ifs with h
  · norm_num
  · apply Real.exp_le_one_iff.mpr
    have : 0 < 2*(1-t) := lt_of_not_ge h
    exact neg_nonpos.mpr (inv_nonneg.mpr this.le)

theorem radial_zero {t : ℝ} (ht : 1 ≤ t) : radial t = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith)

theorem radial_endpoint_derivative : deriv radial 1 = 0 := by
  have hg : HasDerivAt expNegInvGlue 0 0 := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) 0
  have hi : HasDerivAt (fun t : ℝ => 2*(1-t)) (-2) 1 := by
    convert ((hasDerivAt_const (1 : ℝ) 1).sub (hasDerivAt_id 1)).const_mul 2 using 1 <;> norm_num
  have hg' : HasDerivAt expNegInvGlue 0 (2*(1-(1 : ℝ))) := by simpa using hg
  have h := hg'.comp (1 : ℝ) hi
  change deriv (fun t : ℝ => expNegInvGlue (2*(1-t))) 1 = 0
  simpa only [Function.comp_def, zero_mul] using h.deriv

theorem angular_contDiff : ContDiff ℝ (⊤ : ℕ∞) angular := by
  unfold angular
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub Real.contDiff_cos)

theorem angular_periodic : Function.Periodic angular (2*Real.pi) := by
  intro φ
  simp only [angular, Real.cos_add_two_pi]

theorem angular_even (φ : ℝ) : angular (-φ) = angular φ := by simp only [angular, Real.cos_neg]

theorem angularComplex_real (φ t : ℝ) :
    (angularComplex φ (t : ℂ)).re = Real.exp (-(1-Real.cos (φ+t))⁻¹) := by
  have he : -(angularDenominator φ (t : ℂ))⁻¹ = ((-(1-Real.cos (φ+t))⁻¹ : ℝ) : ℂ) := by
    simp only [angularDenominator, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cos, Complex.ofReal_add]
  rw [angularComplex, he, Complex.exp_ofReal_re]

theorem angular_gevrey_regular (φ : ℝ) (hφ : Real.cos φ < 1) (K : ℕ) :
    |iteratedDeriv K angular φ| ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 := by
  have he : (fun t : ℝ => angular (φ+t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (angularComplex φ t).re) := by
    have hc : Continuous (fun t : ℝ => Real.cos (φ+t)) := by fun_prop
    have hn : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), Real.cos (φ+t) < 1 :=
      hc.continuousAt.eventually (eventually_lt_nhds (by simpa using hφ))
    filter_upwards [hn] with t ht
    rw [angularComplex_real]
    simp only [angular, expNegInvGlue, ite_eq_right (by linarith : ¬ (1-Real.cos (φ+t) ≤ 0))]
  have han : AnalyticOnNhd ℂ (angularComplex φ) (ball (0 : ℂ) ((1-Real.cos φ)/100)) :=
    (angularComplex_diffContOnCl φ hφ).1.analyticOnNhd isOpen_ball
  have hd := he.iteratedDeriv_eq K
  simp only [iteratedDeriv_comp_const_add, add_zero] at hd
  rw [
    Well.iteratedDeriv_real_of_complex (angularComplex φ) _ isOpen_ball han K 0
      (by simpa using (show 0 < (1-Real.cos φ)/100 by positivity))] at hd
  rw [hd]
  exact (Complex.abs_re_le_norm _).trans (angularComplex_gevrey φ hφ K)

theorem angular_gevrey_zero (K : ℕ) :
    |iteratedDeriv K angular 0| ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 := by
  have hc : IsClosed {φ : ℝ | |iteratedDeriv K angular φ| ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2} :=
    isClosed_le (angular_contDiff.continuous_iteratedDeriv K (by simp)).abs continuous_const
  have hsub : Ioo (0 : ℝ) Real.pi ⊆
      {φ : ℝ | |iteratedDeriv K angular φ| ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2} := by
    intro φ hφ
    apply angular_gevrey_regular
    apply lt_of_le_of_ne (Real.cos_le_one φ)
    intro he
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hφ.1])
      (by linarith [Real.pi_pos, hφ.2])).mp he
    linarith [hφ.1]
  apply closure_minimal hsub hc
  rw [closure_Ioo (ne_of_lt Real.pi_pos)]
  exact ⟨le_rfl, Real.pi_pos.le⟩

theorem angular_gevrey (φ : ℝ) (K : ℕ) :
    |iteratedDeriv K angular φ| ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 := by
  by_cases hφ : Real.cos φ < 1
  · exact angular_gevrey_regular φ hφ K
  have hc : Real.cos φ = 1 := le_antisymm (Real.cos_le_one φ) (le_of_not_gt hφ)
  have hs : Real.sin φ = 0 := by
    have h := Real.sin_sq_add_cos_sq φ
    rw [hc] at h
    nlinarith [sq_nonneg (Real.sin φ)]
  have he : (fun t : ℝ => angular (φ+t)) = angular := by
    funext t
    simp only [angular, Real.cos_add, hc, hs, one_mul, zero_mul, sub_zero]
  have hd := congrArg (fun f : ℝ → ℝ => iteratedDeriv K f 0) he
  simp only [iteratedDeriv_comp_const_add, add_zero] at hd
  rw [hd]
  exact angular_gevrey_zero K

theorem angular_derivative_periodic (K : ℕ) :
    Function.Periodic (iteratedDeriv K angular) (2*Real.pi) := by
  have he : (fun t => angular (t+2*Real.pi)) = angular := funext angular_periodic
  intro φ
  have h := congrArg (fun f : ℝ → ℝ => iteratedDeriv K f φ) he
  simpa only [iteratedDeriv_comp_add_const] using h

#print axioms angular_gevrey
#print axioms radial_endpoint_derivative

end Maxwell.Continuum.Profile
