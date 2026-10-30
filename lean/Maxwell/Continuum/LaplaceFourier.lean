import Maxwell.Continuum.LaplaceSquaredKernel

/-! Exact Fourier transform of a one-sided complex Laplace moment and
its inversion. This proves the squared-pole Fourier integral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology FourierTransform

def halfMoment (a : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (fun t => (t : ℂ)*Complex.exp (a*t))

theorem halfMoment_integrable {a : ℂ} (ha : a.re < 0) : Integrable (halfMoment a) :=
  (integrableOn_linear_exp ha).integrable_indicator measurableSet_Ioi

theorem halfMoment_continuousAt (a : ℂ) {T : ℝ} (hT : 0 < T) : ContinuousAt (halfMoment a) T := by
  have he : halfMoment a =ᶠ[𝓝 T] (fun t => (t : ℂ)*Complex.exp (a*t)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
    exact indicator_of_mem ht _
  exact (show Continuous (fun t : ℝ => (t : ℂ)*Complex.exp (a*t)) by fun_prop).continuousAt
    |>.congr_of_eventuallyEq he

theorem halfMoment_fourier {a : ℂ} (ha : a.re < 0) (u : ℝ) :
    𝓕 (halfMoment a) u = squareKernel a (2*Real.pi*u) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun t : ℝ => Complex.exp ((-2*Real.pi*t*u : ℝ)*I) • halfMoment a t) =
      (Ioi (0 : ℝ)).indicator
        (fun t => (t : ℂ)*Complex.exp ((a-((2*Real.pi*u : ℝ) : ℂ)*I)*t)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [halfMoment, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
      calc
        _ = (t : ℂ)*(Complex.exp ((-2*Real.pi*t*u : ℝ)*I)*Complex.exp (a*t)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring
    · rw [halfMoment, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [he, integral_indicator measurableSet_Ioi]
  apply integral_linear_exp
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using ha

theorem halfMoment_fourier_integrable {a : ℂ} (ha : a.re < 0) :
    Integrable (𝓕 (halfMoment a)) := by
  have he : 𝓕 (halfMoment a) = (fun u => squareKernel a (2*Real.pi*u)) :=
    funext (halfMoment_fourier ha)
  rw [he]
  simpa only [mul_assoc] using (squareKernel_integrable ha).comp_mul_left' (show (2*Real.pi : ℝ) ≠ 0 by positivity)

theorem squareKernel_fourier_inversion {a : ℂ} (ha : a.re < 0) {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, Complex.exp (((2*Real.pi*u*T : ℝ) : ℂ)*I) *
      squareKernel a (2*Real.pi*u)) = (T : ℂ)*Complex.exp (a*T) := by
  have hi := (halfMoment_integrable ha).fourierInv_fourier_eq (halfMoment_fourier_integrable ha)
    (halfMoment_continuousAt a hT)
  rw [Real.fourierInv_eq'] at hi
  simp_rw [halfMoment_fourier ha] at hi
  rw [halfMoment, indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT)] at hi
  simpa only [smul_eq_mul, RCLike.inner_apply, conj_trivial,
    mul_assoc, mul_comm, mul_left_comm] using hi

#print axioms squareKernel_fourier_inversion

end Maxwell.Continuum.OscillatoryPole
