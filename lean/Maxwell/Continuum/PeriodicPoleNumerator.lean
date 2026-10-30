import Maxwell.Continuum.PeriodicPolePlane
import Maxwell.Continuum.PeriodicPoleSource
import Maxwell.Continuum.AnalyticLineLipschitz

/-! The actual source numerator near the constructed pole. Holomorphic
curve restrictions and their uniform bounds give a quantitative local
Lipschitz estimate with no assumed joint regularity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass Set Metric
open scoped NNReal

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transversePole realMode scaledSourceProduct sourceFactor

def scaledPoleCenter {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : Momentum :=
  (((imaginaryPole D hh j / h : ℝ) : ℂ) * Complex.I) • basisVector j

theorem scaledPoleCenter_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ‖scaledPoleCenter D hh j‖ ≤ 1 := by
  simp only [scaledPoleCenter, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, basisVector_norm, mul_one,
    abs_of_pos (div_pos (imaginaryPole_pos D hh j) D.h_pos)]
  exact imaginaryPole_scaled_le_one D hh j

theorem scaledPoleCenter_physical {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) :
    (h : ℂ) • (scaledPoleCenter D hh j + k) = poleMomentum D hh j k := by
  unfold scaledPoleCenter poleMomentum poleCenter
  rw [smul_add, smul_smul]
  congr 2
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr D.h_pos.ne']

def selectedPoleNumerator {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) : ℂ :=
  scaledSourceProduct h (realMode D hh) (scaledPoleCenter D hh j + k)

theorem selectedPoleNumerator_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1) :
    ‖selectedPoleNumerator D hh j k‖ ≤ (2 : ℝ)^64 := by
  apply scaledSourceProduct_norm_ledger D.h_pos (realMode_norm D hh).le
  · rw [scaledPoleCenter_physical]
    exact poleMomentum_mem_chart D hh j hk
  · have hn := (norm_add_le (scaledPoleCenter D hh j) k).trans (add_le_add (scaledPoleCenter_norm D hh j) hk)
    have hi := sourceImaginary_norm_le (scaledPoleCenter D hh j + k)
    linarith only [hi, hn]

theorem selectedPoleNumerator_curve_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3)
    {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hmap : ∀ ζ ∈ U, ‖g ζ‖ < 1) :
    AnalyticOnNhd ℂ (fun ζ => selectedPoleNumerator D hh j (g ζ)) U := by
  apply scaledSourceProduct_curve_analytic D.h_pos (realMode D hh) hU
    (fun ζ hζ => analyticAt_const.add (hg ζ hζ))
  intro ζ hζ
  change (h : ℂ) • (scaledPoleCenter D hh j + g ζ) ∈ physicalChart
  rw [scaledPoleCenter_physical]
  exact poleMomentum_mem_chart D hh j (hmap ζ hζ).le

theorem selectedPoleNumerator_line_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (a v : Momentum) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => selectedPoleNumerator D hh j (a + ζ • v))
      {ζ | ‖a + ζ • v‖ < 1} := by
  apply selectedPoleNumerator_curve_analytic D hh j
    (isOpen_lt (by fun_prop) continuous_const)
    (fun _ _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  intro ζ hζ
  exact hζ

theorem selectedPoleNumerator_lipschitz {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    LipschitzOnWith ((2 : ℝ≥0)^66) (selectedPoleNumerator D hh j) (closedBall 0 (1 / 8)) := by
  have he := AnalyticLineLipschitz.lipschitzOn (C := (2 : ℝ)^64) (by positivity)
    (selectedPoleNumerator_line_analytic D hh j)
    (fun k hk => selectedPoleNumerator_bound D hh j hk.le)
  have hc : (2 : ℝ≥0)^66 = ⟨4 * (2 : ℝ)^64, by positivity⟩ := by
    ext
    change (2 : ℝ)^66 = 4 * (2 : ℝ)^64
    norm_num
  rw [hc]
  exact he

theorem selectedPoleNumerator_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1 / 8) :
    ‖selectedPoleNumerator D hh j k - selectedPoleNumerator D hh j 0‖ ≤ (2 : ℝ)^66 * ‖k‖ := by
  have he := (selectedPoleNumerator_lipschitz D hh j).dist_le_mul k
    (by simpa only [mem_closedBall, dist_zero_right] using hk) 0 (by simp)
  simpa only [dist_eq_norm, sub_zero, NNReal.coe_pow, NNReal.coe_ofNat] using he

theorem selectedPoleNumerator_zero_positive {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    star (selectedPoleNumerator D hh j 0) = selectedPoleNumerator D hh j 0 ∧
      1 / (2 : ℝ)^96 ≤ (selectedPoleNumerator D hh j 0).re := by
  simpa only [selectedPoleNumerator, scaledPoleCenter, add_zero] using actualSourceProduct_at_pole D hh j

end Maxwell.Continuum.PeriodicBand
