import Maxwell.Continuum.PeriodicGlobalInverse
import Maxwell.Continuum.PeriodicPoleNumerator

/-! The actual source numerator on the full growing rescaled chart.
Real momentum does not increase its exponential weight, so every
derivative used in integration by parts has a uniform bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass Set Metric

attribute [local irreducible] selectedPoleNumerator scaledSourceProduct realMode imaginaryPole
  poleMomentum dielectricBand

theorem sourceImaginary_realMomentum (k : Space) :
    sourceImaginary (realMomentum k.ofLp) = 0 := by
  apply PiLp.ext
  intro i
  change ((k i : ℂ).im) = 0
  exact Complex.ofReal_im _

theorem globalPole_source_imaginary {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) :
    ‖sourceImaginary (scaledPoleCenter D hh j + realMomentum k.ofLp)‖ ≤ 2 := by
  rw [sourceImaginary_add, sourceImaginary_realMomentum, add_zero]
  exact (sourceImaginary_norm_le _).trans
    ((mul_le_mul_of_nonneg_left (scaledPoleCenter_norm D hh j) (by norm_num)).trans_eq (mul_one _))

theorem globalPole_source_physical {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) :
    ‖(h : ℂ) • (scaledPoleCenter D hh j + realMomentum k.ofLp)‖ ≤ analyticRadius/2 := by
  rw [scaledPoleCenter_physical]
  have he := globalPole_momentum_chart D hh j k hk (v := (0 : Momentum))
    (by simp) (ζ := (0 : ℂ)) (by
      rw [norm_zero]
      exact (mul_pos (by norm_num) (globalPoleRadius_pos k)).le)
  simp only [zero_smul, add_zero] at he
  exact he.trans (by norm_num [separatedRadius, analyticRadius, backgroundAmplitude])

theorem globalPole_source_line_analyticAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (v : Momentum) :
    AnalyticAt ℂ (fun ζ : ℂ => selectedPoleNumerator D hh j (realMomentum k.ofLp + ζ • v)) 0 := by
  have ha := scaledSourceProduct_line_analytic D.h_pos (realMode D hh)
    (scaledPoleCenter D hh j + realMomentum k.ofLp) v
  have hmem : (0 : ℂ) ∈ {ζ : ℂ | (h : ℂ) •
      (scaledPoleCenter D hh j + realMomentum k.ofLp + ζ • v) ∈ physicalChart} := by
    simp only [Set.mem_ofPred_eq, zero_smul, add_zero]
    intro i
    exact (norm_le_pi_norm _ i).trans_lt ((globalPole_source_physical D hh j k hk).trans_lt
      (by linarith only [analyticRadius_pos]))
  simpa only [selectedPoleNumerator, add_assoc] using ha 0 hmem

theorem globalPole_source_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {n : ℕ} (hn : n ≤ 32) :
    ‖iteratedDeriv n (fun ζ : ℂ =>
      selectedPoleNumerator D hh j (realMomentum k.ofLp + ζ • v)) 0‖ ≤ (2 : ℝ)^352 := by
  have hi := (globalPole_source_imaginary D hh j k).trans (by norm_num : (2 : ℝ) ≤ 8)
  have he := actualSourceProduct_derivative_le D hh
    (globalPole_source_physical D hh j k hk) hi hv hn
  simpa only [selectedPoleNumerator, add_assoc] using he

end Maxwell.Continuum.PeriodicBand
