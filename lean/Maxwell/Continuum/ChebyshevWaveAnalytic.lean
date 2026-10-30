import Maxwell.Continuum.ProfileAngularComplex
import Maxwell.Continuum.WellRealDeriv

/-! Analytic derivative bounds for the angular form of a single real-frequency plane wave. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Filter Metric
open scoped Topology

theorem iteratedDeriv_comp_ofReal (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (K : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ U) :
    iteratedDeriv K (fun t : ℝ => f (t : ℂ)) x=iteratedDeriv K f (x : ℂ) := by
  induction K generalizing x with
  | zero => simp
  | succ K ih =>
    have he : iteratedDeriv K (fun t : ℝ => f (t : ℂ)) =ᶠ[𝓝 x]
        (fun t : ℝ => iteratedDeriv K f (t : ℂ)) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hmem] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have ha : AnalyticAt ℂ (iteratedDeriv K f) (x : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using (hf.iterated_deriv K) x hx
    simpa only [iteratedDeriv_succ] using ha.differentiableAt.hasDerivAt.comp_ofReal.deriv

def waveAngular (k φ : ℝ) : ℂ := Complex.exp (Complex.I*(k : ℂ)*(Real.cos φ : ℂ))
def waveComplex (k φ : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I*(k : ℂ)*Complex.cos ((φ : ℂ)+z))

theorem waveComplex_diff (k φ : ℝ) : Differentiable ℂ (waveComplex k φ) := by
  unfold waveComplex
  fun_prop

theorem complex_cos_unit_bound (φ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.cos ((φ : ℂ)+z)‖ ≤ 4 := by
  have hd := complex_cos_displacement φ hz
  rw [Complex.ofReal_cos] at hd
  have hc : ‖Complex.cos (φ : ℂ)‖ ≤ 1 := by
    simpa only [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one φ
  have ht : ‖Complex.cos ((φ : ℂ)+z)‖ ≤
      ‖Complex.cos ((φ : ℂ)+z)-Complex.cos (φ : ℂ)‖+‖Complex.cos (φ : ℂ)‖ :=
    norm_le_norm_sub_add _ _
  linarith

theorem waveComplex_norm (k φ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖waveComplex k φ z‖ ≤ Real.exp (4*|k|) := by
  rw [waveComplex, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  apply (Complex.re_le_norm _).trans
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (complex_cos_unit_bound φ hz) (abs_nonneg k)
  exact h.trans_eq (by ring)

theorem waveComplex_derivative_bound (k φ : ℝ) (K : ℕ) :
    ‖iteratedDeriv K (waveComplex k φ) 0‖ ≤ (K.factorial : ℝ)*Real.exp (4*|k|) := by
  have hd : DiffContOnCl ℂ (waveComplex k φ) (ball (0 : ℂ) 1) :=
    ⟨(waveComplex_diff k φ).differentiableOn, (waveComplex_diff k φ).continuous.continuousOn⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le K
    (by norm_num : (0 : ℝ)<1) hd (fun z hz => waveComplex_norm k φ (mem_sphere_zero_iff_norm.mp hz).le)
  simpa only [one_pow, div_one] using h

theorem waveComplex_real (k φ t : ℝ) : waveComplex k φ (t : ℂ)=waveAngular k (φ+t) := by
  simp only [waveComplex, waveAngular, Complex.ofReal_add, Complex.ofReal_cos]

theorem waveAngular_derivative_bound (k φ : ℝ) (K : ℕ) :
    ‖iteratedDeriv K (waveAngular k) φ‖ ≤ (K.factorial : ℝ)*Real.exp (4*|k|) := by
  have he : (fun t : ℝ => waveComplex k φ (t : ℂ))=(fun t => waveAngular k (φ+t)) :=
    funext (waveComplex_real k φ)
  have hi := iteratedDeriv_comp_ofReal (waveComplex k φ) univ isOpen_univ
    ((waveComplex_diff k φ).differentiableOn.analyticOnNhd isOpen_univ) K 0 (mem_univ _)
  rw [he, iteratedDeriv_comp_const_add] at hi
  simp only [add_zero, Complex.ofReal_zero] at hi
  rw [hi]
  exact waveComplex_derivative_bound k φ K

theorem waveAngular_periodic (k : ℝ) : Function.Periodic (waveAngular k) (2*Real.pi) := by
  intro φ
  simp only [waveAngular, Real.cos_add_two_pi]

theorem waveAngular_even (k φ : ℝ) : waveAngular k (-φ)=waveAngular k φ := by
  simp only [waveAngular, Real.cos_neg]

theorem waveAngular_norm (k φ : ℝ) : ‖waveAngular k φ‖=1 := by
  simp only [waveAngular, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

#print axioms waveAngular_derivative_bound

end Maxwell.Continuum.Profile
