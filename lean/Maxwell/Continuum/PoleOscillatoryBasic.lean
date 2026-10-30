import Maxwell.Continuum.PoleSquareIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Derivatives and vanishing endpoint terms for the simple pole on
the real integration line. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology

def poleSimple (p : ℂ) (u : ℝ) : ℂ := 1/((u : ℂ)-p)

theorem real_sub_pole_ne_zero {p : ℂ} (hp : 0 < p.im) (u : ℝ) : (u : ℂ)-p ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at hi
  exact hp.ne' hi

theorem poleSimple_hasDerivAt {p : ℂ} (hp : 0 < p.im) (u : ℝ) :
    HasDerivAt (poleSimple p) (-poleSquare p u) u := by
  have hd := (((hasDerivAt_id u).ofReal_comp).sub_const p).inv (real_sub_pole_ne_zero hp u)
  convert hd using 1
  · funext x
    simp only [poleSimple, id_eq, one_div, Pi.inv_apply]
  · simp only [poleSquare, id_eq, Complex.ofReal_one, neg_div]

theorem poleSimple_continuous {p : ℂ} (hp : 0 < p.im) : Continuous (poleSimple p) :=
  continuous_iff_continuousAt.mpr (fun u => (poleSimple_hasDerivAt hp u).continuousAt)

theorem oscillatoryPhase_hasDerivAt (T u : ℝ) :
    HasDerivAt (oscillatoryPhase T) ((I*(T : ℂ))*oscillatoryPhase T u) u := by
  have hd := ((((hasDerivAt_id u).const_mul T).ofReal_comp).mul_const I).cexp
  convert hd using 1
  · rfl
  · simp only [oscillatoryPhase, id_eq, mul_one]
    ring

theorem poleSimple_tendsto_zero_atTop (p : ℂ) : Tendsto (poleSimple p) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hd : Tendsto (fun u : ℝ => ‖(u : ℂ)-p‖) atTop atTop := by
    have hr : Tendsto (fun u : ℝ => u-p.re) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-p.re) tendsto_id
    apply tendsto_atTop_mono (fun u => ?_) hr
    simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.re_le_norm ((u : ℂ)-p)
  convert tendsto_inv_atTop_zero.comp hd using 1
  funext u
  simp only [poleSimple, one_div, norm_inv, Function.comp_apply]

theorem poleSimple_tendsto_zero_atBot (p : ℂ) : Tendsto (poleSimple p) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hd : Tendsto (fun u : ℝ => ‖(u : ℂ)-p‖) atBot atTop := by
    have hr : Tendsto (fun u : ℝ => p.re-u) atBot atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_left atBot p.re tendsto_neg_atBot_atTop
    apply tendsto_atTop_mono (fun u => ?_) hr
    have he := Complex.re_le_norm (p-(u : ℂ))
    simpa only [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] using he
  convert tendsto_inv_atTop_zero.comp hd using 1
  funext u
  simp only [poleSimple, one_div, norm_inv, Function.comp_apply]

theorem phase_pole_tendsto_zero_atTop (p : ℂ) (T : ℝ) :
    Tendsto (fun u => oscillatoryPhase T u*poleSimple p u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_mul, oscillatoryPhase_norm, one_mul]
  simpa only [norm_zero] using (poleSimple_tendsto_zero_atTop p).norm

theorem phase_pole_tendsto_zero_atBot (p : ℂ) (T : ℝ) :
    Tendsto (fun u => oscillatoryPhase T u*poleSimple p u) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_mul, oscillatoryPhase_norm, one_mul]
  simpa only [norm_zero] using (poleSimple_tendsto_zero_atBot p).norm

#print axioms phase_pole_tendsto_zero_atTop

end Maxwell.Continuum.OscillatoryPole
