import Maxwell.Continuum.PoleOscillatoryBasic

/-! The longitudinal simple-pole integral is an improper oscillatory
integral. It is derived from the absolutely convergent squared-pole
Fourier integral and finite-interval integration by parts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology

theorem oscillatory_pole_interval {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : 0 < T)
    (a b : ℝ) :
    (∫ u in a..b, oscillatoryPhase T u*poleSimple p u) =
      (oscillatoryPhase T b*poleSimple p b - oscillatoryPhase T a*poleSimple p a +
        ∫ u in a..b, oscillatoryPhase T u*poleSquare p u)/(I*(T : ℂ)) := by
  have hc : I*(T : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hT.ne')
  have hf : Continuous (fun u => oscillatoryPhase T u*poleSimple p u) :=
    (continuous_iff_continuousAt.mpr fun u =>
      (oscillatoryPhase_hasDerivAt T u).continuousAt).mul (poleSimple_continuous hp)
  have hi : IntervalIntegrable (fun u => oscillatoryPhase T u*poleSimple p u) volume a b :=
    hf.intervalIntegrable a b
  have hs := (oscillatory_poleSquare_integrable hp T).intervalIntegrable (a := a) (b := b)
  have hd (u : ℝ) : HasDerivAt (fun v => oscillatoryPhase T v*poleSimple p v)
      ((I*(T : ℂ))*(oscillatoryPhase T u*poleSimple p u) -
        oscillatoryPhase T u*poleSquare p u) u := by
    convert (oscillatoryPhase_hasDerivAt T u).mul (poleSimple_hasDerivAt hp u) using 1
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hi.const_mul (I*(T : ℂ))).sub hs)
  rw [intervalIntegral.integral_sub (hi.const_mul _) hs,
    intervalIntegral.integral_const_mul] at he
  apply (eq_div_iff hc).2
  linear_combination he

theorem oscillatory_pole_integral {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R : ℝ => ∫ u in -R..R, oscillatoryPhase T u*poleSimple p u)
      atTop (𝓝 (((2*Real.pi : ℝ) : ℂ)*I*Complex.exp (I*p*T))) := by
  have hB : Tendsto (fun R : ℝ => oscillatoryPhase T R*poleSimple p R -
      oscillatoryPhase T (-R)*poleSimple p (-R)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [sub_zero, Function.comp_apply] using (phase_pole_tendsto_zero_atTop p T).sub
      ((phase_pole_tendsto_zero_atBot p T).comp tendsto_neg_atTop_atBot)
  have hS := intervalIntegral_tendsto_integral (oscillatory_poleSquare_integrable hp T)
    tendsto_neg_atTop_atBot tendsto_id
  rw [oscillatory_poleSquare_integral hp hT] at hS
  have hlim := (hB.add hS).div_const (I*(T : ℂ))
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have he : (0 + -((2*Real.pi*T : ℝ) : ℂ)*Complex.exp (I*p*T))/(I*(T : ℂ)) =
      ((2*Real.pi : ℝ) : ℂ)*I*Complex.exp (I*p*T) := by
    push_cast
    field_simp
    simp only [I_sq]
    ring
  rw [he] at hlim
  exact hlim.congr (fun R => (oscillatory_pole_interval hp hT (-R) R).symm)

#print axioms oscillatory_pole_integral

end Maxwell.Continuum.OscillatoryPole
