import Maxwell.Continuum.PeriodicPoleContractionBounds
import Maxwell.Continuum.AnalyticFixedPointAnalytic

/-! A constructed analytic transverse pole of the literal periodic Maxwell
band, on fixed radii independent of inverse length. Existence, uniqueness,
and quadratic smallness follow from the proved scalar contraction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric
open scoped NNReal

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope

theorem poleMap_maps {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : w ∈ ball 0 transversePoleRadius) :
    MapsTo (poleMap D hh j w) (closedBall 0 longitudinalPoleRadius)
      (closedBall 0 longitudinalPoleRadius) := by
  have hw' : ‖w‖ ≤ transversePoleRadius :=
    le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw)
  have hwHalf : ‖w‖ ≤ 1 / 2 := hw'.trans
    (pole_radii.2.2.1.trans (pole_radii.2.2.2.1.trans (by norm_num)))
  have hzero : ‖poleMap D hh j w 0‖ ≤ longitudinalPoleRadius / 2 :=
    (poleMap_zero_bound D hh j hwHalf).trans
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw' 2) (by positivity)).trans
        pole_radii.2.2.2.2.2)
  intro u hu
  have hnorm : ‖u‖ ≤ longitudinalPoleRadius := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hlip := (poleMap_lipschitz D hh j hw').dist_le_mul u hu 0
    (mem_closedBall_self pole_radii.1.le)
  have hd : ‖poleMap D hh j w u - poleMap D hh j w 0‖ ≤ (1 / 2 : ℝ) * ‖u‖ := by
    simpa only [dist_eq_norm, sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hlip
  rw [mem_closedBall, dist_zero_right]
  have ht := norm_add_le (poleMap D hh j w u - poleMap D hh j w 0) (poleMap D hh j w 0)
  rw [sub_add_cancel] at ht
  linarith only [ht, hd, hnorm, hzero]

theorem poleContractionData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticFixedPoint.Data (poleMap D hh j) (ball 0 transversePoleRadius)
      0 longitudinalPoleRadius (1 / 2) where
  radius_pos := pole_radii.1
  constant_lt_one := by norm_num
  maps _ hw := poleMap_maps D hh j hw
  lipschitz _ hw := poleMap_lipschitz D hh j
    (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw))

def transversePole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : Momentum → ℂ :=
  (poleContractionData D hh j).point

theorem transversePole_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) :
    ‖transversePole D hh j w‖ ≤ longitudinalPoleRadius := by
  unfold transversePole
  simpa only [mem_closedBall, dist_zero_right] using
    (poleContractionData D hh j).point_mem w (by simpa only [mem_ball, dist_zero_right] using hw)

theorem transversePole_equation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) :
    poleDenominator D hh j (poleOffset j w (transversePole D hh j w)) = 0 := by
  have he := (poleContractionData D hh j).point_fixed w
    (by simpa only [mem_ball, dist_zero_right] using hw)
  change transversePole D hh j w -
    poleDenominator D hh j (poleOffset j w (transversePole D hh j w)) /
      ((poleSlope D hh j : ℂ) * Complex.I) = transversePole D hh j w at he
  exact (div_eq_zero_iff.mp (sub_eq_self.mp he)).resolve_right (poleSlope_ne_zero D hh j)

theorem transversePole_unique {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius)
    (he : poleDenominator D hh j (poleOffset j w u) = 0) :
    u = transversePole D hh j w := by
  apply (poleContractionData D hh j).point_unique w
    (by simpa only [mem_ball, dist_zero_right] using hw)
    (by simpa only [mem_closedBall, dist_zero_right] using hu)
  simp only [poleMap, he, zero_div, sub_zero]

theorem transversePole_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : transversePole D hh j 0 = 0 := by
  apply Eq.symm
  apply transversePole_unique D hh j (by simpa only [norm_zero] using pole_radii.2.1)
    (by simpa only [norm_zero] using pole_radii.1.le)
  rw [poleOffset_zero, poleDenominator_zero]

theorem transversePole_quadratic_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) :
    ‖transversePole D hh j w‖ ≤ (2 : ℝ)^122 * ‖w‖^2 := by
  have h := (poleContractionData D hh j).residual_bound w
    (by simpa only [mem_ball, dist_zero_right] using hw)
    (z := 0) (mem_closedBall_self pole_radii.1.le)
  have hb := poleMap_zero_bound D hh j
    (hw.le.trans (pole_radii.2.2.1.trans (pole_radii.2.2.2.1.trans (by norm_num))))
  change dist 0 (transversePole D hh j w) ≤
    dist 0 (poleMap D hh j w 0) / (1 - ((1 / 2 : ℝ≥0) : ℝ)) at h
  simp only [dist_zero_left, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at h
  have hc : 2 * (2 : ℝ)^121 = (2 : ℝ)^122 := by norm_num
  calc
    _ ≤ ‖poleMap D hh j w 0‖ / (1 - (1 / 2 : ℝ)) := h
    _ ≤ ((2 : ℝ)^121 * ‖w‖^2) / (1 - (1 / 2 : ℝ)) :=
      div_le_div_of_nonneg_right hb (by norm_num)
    _ = (2 * (2 : ℝ)^121) * ‖w‖^2 := by ring
    _ = _ := by rw [hc]

theorem poleMap_joint_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (Function.uncurry (poleMap D hh j))
      (ball 0 transversePoleRadius ×ˢ closedBall 0 longitudinalPoleRadius) := by
  rintro ⟨w, u⟩ ⟨hw, hu⟩
  have hw' : ‖w‖ ≤ transversePoleRadius :=
    le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw)
  have hu' : ‖u‖ ≤ longitudinalPoleRadius := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hk := poleOffset_norm_le pole_radii.1.le j (hw'.trans pole_radii.2.2.1) hu'
  have ha := poleDenominator_analytic D hh j (poleOffset j w u)
    (by rw [mem_ball, dist_zero_right]; linarith only [hk, pole_radii.2.2.2.1])
  have hb := AnalyticAt.comp (f := fun a : Momentum × ℂ => poleOffset j a.1 a.2) ha
    (poleOffset_analytic j (w, u))
  change AnalyticAt ℂ (fun a : Momentum × ℂ => a.2 -
    poleDenominator D hh j (poleOffset j a.1 a.2) / ((poleSlope D hh j : ℂ) * Complex.I)) (w, u)
  convert! analyticAt_snd.sub (hb.mul (analyticAt_const
    (v := (((poleSlope D hh j : ℂ) * Complex.I)⁻¹)))) using 1

theorem transversePole_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (transversePole D hh j) (ball 0 transversePoleRadius) :=
  (poleContractionData D hh j).analyticOnNhd_point (poleMap_joint_analytic D hh j) isOpen_ball

end Maxwell.Continuum.PeriodicBand
