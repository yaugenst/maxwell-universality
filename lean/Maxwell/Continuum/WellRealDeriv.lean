import Maxwell.Continuum.WellComplex
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Transfer of the explicit complex-line estimates to real directional derivatives. -/

noncomputable section

namespace Maxwell.Continuum.Well

open Set Filter Metric
open scoped Topology

theorem iteratedDeriv_real_of_complex (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (K : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ U) :
    iteratedDeriv K (fun t : ℝ => (f t).re) x = (iteratedDeriv K f x).re := by
  induction K generalizing x with
  | zero => simp
  | succ K ih =>
    have he : iteratedDeriv K (fun t : ℝ => (f t).re) =ᶠ[𝓝 x]
        (fun t : ℝ => (iteratedDeriv K f t).re) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ U :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hmem] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have ha : AnalyticAt ℂ (iteratedDeriv K f) (x : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using (hf.iterated_deriv K) x hx
    simpa only [iteratedDeriv_succ] using ha.differentiableAt.hasDerivAt.real_of_complex.deriv

def directionalDerivative (K : ℕ) (f : Space → ℝ) (y v : Space) : ℝ :=
  iteratedFDeriv ℝ K f y (fun _ => v)

theorem directionalDerivative_eq_line (K : ℕ) (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y v : Space) :
    directionalDerivative K f y v = iteratedDeriv K (fun t : ℝ => f (y + t • v)) 0 := by
  let L : ℝ →L[ℝ] Space := (1 : ℝ →L[ℝ] ℝ).smulRight v
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space => f (y + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have h := L.iteratedFDeriv_comp_right hg 0 (i := K) (by simp)
  have he : (fun z : Space => f (y + z)) ∘ L = (fun t : ℝ => f (y + t • v)) := rfl
  rw [he] at h
  rw [iteratedDeriv, h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [L, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    zero_smul, one_smul]
  rw [iteratedFDeriv_comp_add_left, add_zero]
  rfl

theorem directionalDerivative_continuous (K : ℕ) (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Space) :
    Continuous (fun y => directionalDerivative K f y v) := by
  exact (continuous_eval_const (fun _ : Fin K => v)).comp
    (hf.continuous_iteratedFDeriv (by simp))

theorem norm_line_sq (y v : Space) (t : ℝ) :
    ‖y + t • v‖ ^ 2 = ‖y‖ ^ 2 + 2 * inner ℝ y v * t + ‖v‖ ^ 2 * t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem complexLineBump_real (c s a b t : ℝ) :
    (complexLineBump c s a b (t : ℂ)).re = Real.exp (-c / (s - 2 * a * t - b * t ^ 2)) := by
  have he : -(c : ℂ) / lineDenominator s a b (t : ℂ) =
      ((-c / (s - 2 * a * t - b * t ^ 2) : ℝ) : ℂ) := by
    simp only [lineDenominator, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  rw [complexLineBump, he, Complex.exp_ofReal_re]

end Maxwell.Continuum.Well
