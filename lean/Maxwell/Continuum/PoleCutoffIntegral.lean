import Maxwell.Continuum.PoleTailBounds
import Maxwell.Continuum.OscillatoryDerivatives

/-! The actual compactly cut off simple-pole integral differs from its
residue by a uniform inverse power of the oscillation length. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter PeriodicBand
open scoped Topology FourierTransform ContDiff

def cutoffPoleIntegral (a : ℝ) (p : ℂ) (T : ℝ) : ℂ :=
  ∫u : ℝ, oscillatoryPhase T u*(complexCutoff a u*poleSimple p u)

theorem poleTail_norm_le (a : ℝ) (p : ℂ) (u : ℝ) : ‖poleTail a p u‖ ≤ ‖poleSimple p u‖ := by
  rw [poleTail, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoffComplement_norm a u)

theorem poleTail_tendsto_zero_atTop (a : ℝ) (p : ℂ) :
    Tendsto (poleTail a p) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (poleTail_norm_le a p)
  simpa only [norm_zero] using (poleSimple_tendsto_zero_atTop p).norm

theorem poleTail_tendsto_zero_atBot (a : ℝ) (p : ℂ) :
    Tendsto (poleTail a p) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (poleTail_norm_le a p)
  simpa only [norm_zero] using (poleSimple_tendsto_zero_atBot p).norm

theorem complexCutoff_hasCompactSupport {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (complexCutoff a) :=
  (scaledPsi_hasCompactSupport ha).comp_left Complex.ofReal_zero

theorem cutoffPole_integrable {a : ℝ} (ha : 0 < a) {p : ℂ} (hp : 0 < p.im) :
    Integrable (fun u => complexCutoff a u*poleSimple p u) :=
  ((complexCutoff_contDiff a).continuous.mul (poleSimple_continuous hp)).integrable_of_hasCompactSupport
    (complexCutoff_hasCompactSupport ha).mul_right

theorem cutoffPole_error_identity {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {p : ℂ}
    (hpim : 0 < p.im) (hp : ‖p‖ ≤ a/2) {T : ℝ} (hT : 0 < T) :
    ((2*Real.pi : ℝ) : ℂ)*I*Complex.exp (I*p*T)-cutoffPoleIntegral a p T =
      -(∫u : ℝ, oscillatoryPhase T u*deriv (poleTail a p) u)/(I*(T : ℂ)) := by
  have hi : Integrable (deriv (poleTail a p)) := by
    simpa only [iteratedDeriv_one] using poleTail_derivative_integrable ha ha1 hpim hp (n := 1) (by omega)
  have hl := oscillatory_first_improper (poleTail_contDiff a hpim) hi
    (poleTail_tendsto_zero_atTop a p) (poleTail_tendsto_zero_atBot a p) hT
  have hc := intervalIntegral_tendsto_integral (phase_mul_integrable (cutoffPole_integrable ha hpim) T)
    tendsto_neg_atTop_atBot tendsto_id
  change Tendsto _ _ (𝓝 (cutoffPoleIntegral a p T)) at hc
  have hd := (oscillatory_pole_integral hpim hT).sub hc
  have he (R : ℝ) :
      (∫u in -R..R, oscillatoryPhase T u*poleSimple p u)-
        (∫u in -R..R, oscillatoryPhase T u*(complexCutoff a u*poleSimple p u)) =
      ∫u in -R..R, oscillatoryPhase T u*poleTail a p u := by
    have hi1 : IntervalIntegrable (fun u => oscillatoryPhase T u*poleSimple p u) volume (-R) R :=
      ((show Continuous (oscillatoryPhase T) from continuous_iff_continuousAt.mpr
        (fun u => (oscillatoryPhase_hasDerivAt T u).continuousAt)).mul (poleSimple_continuous hpim)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1
      ((phase_mul_integrable (cutoffPole_integrable ha hpim) T).intervalIntegrable)]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [poleTail, cutoffComplement]
    ring
  exact tendsto_nhds_unique (hd.congr he) hl

theorem cutoffPole_error_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {p : ℂ}
    (hpim : 0 < p.im) (hp : ‖p‖ ≤ a/2) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖cutoffPoleIntegral a p T-((2*Real.pi : ℝ) : ℂ)*I*Complex.exp (I*p*T)‖ ≤
      tailDerivativeBound a (n+1)*Real.pi/T^(n+1) := by
  have hf := poleTail_contDiff a hpim
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv (poleTail a p)) := (contDiff_infty_iff_deriv.mp hf).2
  have hi (k : ℕ) (_ : (k : ℕ∞) ≤ ⊤) : Integrable (iteratedDeriv k (deriv (poleTail a p))) := by
    rw [← iteratedDeriv_succ']
    exact poleTail_derivative_integrable ha ha1 hpim hp (by omega)
  have he := oscillatory_norm_iteratedDeriv hd hi (n := n) (by simp) hT.le
  rw [← iteratedDeriv_succ'] at he
  have hbound : T^n*‖∫u : ℝ, oscillatoryPhase T u*deriv (poleTail a p) u‖ ≤
      tailDerivativeBound a (n+1)*Real.pi := by
    rw [← he]
    calc
      _ ≤ ∫u : ℝ, ‖oscillatoryPhase T u*iteratedDeriv (n+1) (poleTail a p) u‖ := norm_integral_le_integral_norm _
      _ = ∫u : ℝ, ‖iteratedDeriv (n+1) (poleTail a p) u‖ := by
        simp only [norm_mul, oscillatoryPhase_norm, one_mul]
      _ ≤ _ := poleTail_derivative_l1 ha ha1 hpim hp (by omega)
  rw [norm_sub_rev, cutoffPole_error_identity ha ha1 hpim hp hT, norm_div, norm_neg,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply (div_le_div_iff₀ hT (pow_pos hT _)).mpr
  rw [pow_succ]
  nlinarith only [mul_le_mul_of_nonneg_right hbound hT.le]

#print axioms cutoffPole_error_bound

end Maxwell.Continuum.OscillatoryPole
