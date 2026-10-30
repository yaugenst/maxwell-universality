import Maxwell.Continuum.PeriodicPoleResidueAmplitude
import Maxwell.Continuum.RankOneBandDivision

/-! Exact scalar division of the actual selected source/Maxwell denominator
at its constructed pole. The regular part is a genuine holomorphic divided
difference, not an unspecified remainder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transversePole selectedPoleNumerator selectedPoleAmplitude

def selectedPoleDivisor {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) (u : ℂ) : ℂ :=
  dslope (fun v => poleDenominator D hh j (poleOffset j w v)) (transversePole D hh j w) u

def selectedRegularFactor {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) (u : ℂ) : ℂ :=
  selectedPoleNumerator D hh j (poleOffset j w u) / selectedPoleDivisor D hh j w u

def selectedRegularPart {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) (u : ℂ) : ℂ :=
  dslope (selectedRegularFactor D hh j w) (transversePole D hh j w) u

theorem poleOffset_scalar_analytic (j : Fin 3) (w : Momentum) (u : ℂ) :
    AnalyticAt ℂ (poleOffset j w) u := by
  have he : poleOffset j w = fun v : ℂ => poleOffset j w 0 + v • basisVector j :=
    funext (poleOffset_add_basis j w)
  rw [he]
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)

theorem poleDenominator_longitudinal_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    AnalyticAt ℂ (fun v => poleDenominator D hh j (poleOffset j w v)) u := by
  have hk := poleOffset_norm_le pole_radii.1.le j (hw.le.trans pole_radii.2.2.1) hu
  exact (poleDenominator_analytic D hh j _
    (by rw [mem_ball, dist_zero_right]; linarith only [hk, pole_radii.2.2.2.1])).comp
    (f := poleOffset j w) (poleOffset_scalar_analytic j w u)

theorem poleDenominator_longitudinal_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    deriv (fun v => poleDenominator D hh j (poleOffset j w v)) u =
      poleLongitudinalDerivative D hh j (poleOffset j w u) := by
  have hk := poleOffset_norm_le pole_radii.1.le j (hw.le.trans pole_radii.2.2.1) hu
  have ha := poleDenominator_analytic D hh j _
    (by rw [mem_ball, dist_zero_right]; linarith only [hk, pole_radii.2.2.2.1])
  exact (ha.differentiableAt.hasFDerivAt.comp_hasDerivAt u (poleOffset_hasDerivAt j w u)).deriv

theorem selectedPoleDivisor_at_pole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    selectedPoleDivisor D hh j w (transversePole D hh j w) =
      poleLongitudinalDerivative D hh j (poleCurve D hh j w) := by
  rw [selectedPoleDivisor, dslope_same,
    poleDenominator_longitudinal_derivative D hh j hw (transversePole_norm D hh j hw)]
  rfl

theorem selectedPoleDivisor_factor {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    (u : ℂ) :
    (u - transversePole D hh j w) * selectedPoleDivisor D hh j w u =
      poleDenominator D hh j (poleOffset j w u) :=
  sub_smul_dslope_of_zero (f := fun v => poleDenominator D hh j (poleOffset j w v))
    (transversePole_equation D hh j hw) u

theorem selectedPoleDivisor_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) : selectedPoleDivisor D hh j w u ≠ 0 := by
  by_cases he : u = transversePole D hh j w
  · subst u
    rw [selectedPoleDivisor_at_pole D hh j hw]
    exact poleCurve_derivative_ne_zero D hh j hw
  · intro hz
    have hf := selectedPoleDivisor_factor D hh j hw u
    rw [hz, mul_zero] at hf
    exact he (transversePole_unique D hh j hw hu hf.symm)

theorem selectedPoleDivisor_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    AnalyticAt ℂ (selectedPoleDivisor D hh j w) u :=
  RankOneBand.analyticAt_dslope
    (poleDenominator_longitudinal_analytic D hh j hw (transversePole_norm D hh j hw))
    (poleDenominator_longitudinal_analytic D hh j hw hu)

theorem selectedPoleNumerator_longitudinal_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    AnalyticAt ℂ (fun v => selectedPoleNumerator D hh j (poleOffset j w v)) u := by
  apply selectedPoleNumerator_curve_analytic D hh j isOpen_ball
    (fun v _ => poleOffset_scalar_analytic j w v) (U := ball 0 (1 / 2)) ?_ u ?_
  · intro v hv
    have hv' : ‖v‖ ≤ 1 / 2 := le_of_lt (by simpa only [mem_ball, dist_zero_right] using hv)
    have hk := poleOffset_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) j
      (hw.le.trans (pole_radii.2.2.1.trans (pole_radii.2.2.2.1.trans (by norm_num)))) hv'
    linarith only [hk]
  · rw [mem_ball, dist_zero_right]
    linarith only [hu, pole_radii.2.2.2.1]

theorem selectedRegularFactor_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    AnalyticAt ℂ (selectedRegularFactor D hh j w) u := by
  exact (selectedPoleNumerator_longitudinal_analytic D hh j hw hu).div
    (selectedPoleDivisor_analytic D hh j hw hu) (selectedPoleDivisor_ne_zero D hh j hw hu)

theorem selectedRegularFactor_at_pole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    selectedRegularFactor D hh j w (transversePole D hh j w) = selectedPoleAmplitude D hh j w := by
  rw [selectedRegularFactor, selectedPoleDivisor_at_pole D hh j hw]
  unfold selectedPoleAmplitude poleCurve
  rfl

theorem selectedRegularPart_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    AnalyticAt ℂ (selectedRegularPart D hh j w) u :=
  RankOneBand.analyticAt_dslope
    (selectedRegularFactor_analytic D hh j hw (transversePole_norm D hh j hw))
    (selectedRegularFactor_analytic D hh j hw hu)

theorem selectedPole_exact_division {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) (hne : u ≠ transversePole D hh j w) :
    selectedPoleNumerator D hh j (poleOffset j w u) / poleDenominator D hh j (poleOffset j w u) =
      selectedPoleAmplitude D hh j w / (u - transversePole D hh j w) + selectedRegularPart D hh j w u := by
  have hs := sub_smul_dslope (selectedRegularFactor D hh j w) (transversePole D hh j w) u
  change (u - transversePole D hh j w) * selectedRegularPart D hh j w u =
    selectedRegularFactor D hh j w u - selectedRegularFactor D hh j w (transversePole D hh j w) at hs
  rw [selectedRegularFactor_at_pole D hh j hw] at hs
  rw [← selectedPoleDivisor_factor D hh j hw u]
  have hdiv := selectedPoleDivisor_ne_zero D hh j hw hu
  have hdiff := sub_ne_zero.mpr hne
  unfold selectedRegularFactor at hs
  field_simp [hdiv, hdiff] at hs ⊢
  linear_combination -hs

#print axioms selectedPole_exact_division
#print axioms selectedRegularPart_analytic

end Maxwell.Continuum.PeriodicBand
