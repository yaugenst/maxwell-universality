import Maxwell.Continuum.PeriodicPoleDivisionBound

/-! The actual transverse pole is purely imaginary for real transverse
momentum. Physical conjugation and longitudinal reflection, followed by
the proved root uniqueness, establish this exact symmetry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric TransverseGaussian

attribute [local irreducible] imaginaryPole dielectricBand poleSlope transversePole

theorem poleMomentum_star_reflect {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) :
    poleMomentum D hh j (FiberReflection.momentum j (star k)) =
      FiberReflection.momentum j (star (poleMomentum D hh j k)) := by
  unfold poleMomentum poleCenter
  rw [star_add, star_smul, star_smul, basisVector_star,
    reflection_add, reflection_smul, reflection_smul, reflect_basis_same]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, neg_smul, smul_neg, neg_neg]

theorem poleDenominator_star_reflect {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1) :
    poleDenominator D hh j (FiberReflection.momentum j (star k)) =
      star (poleDenominator D hh j k) := by
  have hq := poleMomentum_mem_chart D hh j hk
  unfold poleDenominator
  rw [poleMomentum_star_reflect, dielectricBand_reflect (physicalChart_star hq), dielectricBand_schwarz hq]
  simp only [star_mul', star_sub, Complex.star_def, map_inv₀, map_pow, Complex.conj_ofReal]

theorem poleOffset_star_reflect (j : Fin 3) {w : Momentum} (hw : star w = w) (u : ℂ) :
    FiberReflection.momentum j (star (poleOffset j w u)) = poleOffset j w (-star u) := by
  funext k
  have hwk : star (w k) = w k := congrFun hw k
  simp only [FiberReflection.momentum, FiberReflection.coordinateSign, Pi.star_apply, poleOffset]
  by_cases hkj : k = j
  · subst k
    simp only [ite_true, neg_one_mul]
  · simp only [ite_eq_right hkj, one_mul, hwk]

theorem transversePole_re_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) (hreal : star w = w) : (transversePole D hh j w).re = 0 := by
  have hk : ‖poleCurve D hh j w‖ ≤ 1 := (poleCurve_norm D hh j hw).trans
    (hw.le.trans (by norm_num [transversePoleRadius]))
  have he := poleDenominator_star_reflect D hh j hk
  change poleDenominator D hh j (FiberReflection.momentum j
    (star (poleOffset j w (transversePole D hh j w)))) = star (poleDenominator D hh j
      (poleOffset j w (transversePole D hh j w))) at he
  rw [poleOffset_star_reflect j hreal, transversePole_equation D hh j hw, star_zero] at he
  have hp := transversePole_unique D hh j hw
    (u := -star (transversePole D hh j w))
    (by simpa only [norm_neg, norm_star] using transversePole_norm D hh j hw) he
  have hr := congrArg Complex.re hp
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at hr
  linarith only [hr]

theorem transverseMomentum_star (j : Fin 3) (x : Plane) : star (transverseMomentum j x) = transverseMomentum j x := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp only [Pi.star_apply, transverseMomentum_same, star_zero]
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hkj
    simp only [Pi.star_apply, transverseMomentum_other, Complex.star_def, Complex.conj_ofReal]

theorem polePlanePhase_re_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {x : Plane} (hx : ‖x‖ < transversePoleRadius) :
    (polePlanePhase D hh j x).re = 0 :=
  transversePole_re_zero D hh j ((transverseMomentum_norm j x).trans_lt hx) (transverseMomentum_star j x)

theorem poleDenominator_distance_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    (1 / 2 : ℝ) * ‖u - transversePole D hh j w‖ ≤ ‖poleDenominator D hh j (poleOffset j w u)‖ := by
  rw [← selectedPoleDivisor_factor D hh j hw u, norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (selectedPoleDivisor_lower D hh j hw hu) (norm_nonneg (u - transversePole D hh j w))

theorem poleDenominator_real_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {x : Plane} (hx : ‖x‖ ≤ poleGaussianRadius)
    {u : ℝ} (hu : |u| ≤ longitudinalPoleRadius) :
    (2 : ℝ)^(-258 : ℤ) * (|u| + ‖x‖^2) ≤
      ‖poleDenominator D hh j (poleOffset j (transverseMomentum j x) (u : ℂ))‖ := by
  have hx' := hx.trans_lt poleGaussianRadius_lt
  have hw := (transverseMomentum_norm j x).trans_lt hx'
  have hre := polePlanePhase_re_zero D hh j hx'
  have him := polePlanePhase_damping D hh j hx
  have hn := poleDenominator_distance_lower D hh j hw (u := (u : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu)
  change (1 / 2 : ℝ) * ‖(u : ℂ) - polePlanePhase D hh j x‖ ≤ _ at hn
  have hreal := Complex.abs_re_le_norm ((u : ℂ) - polePlanePhase D hh j x)
  have himag := Complex.abs_im_le_norm ((u : ℂ) - polePlanePhase D hh j x)
  simp only [Complex.sub_re, Complex.ofReal_re, hre, sub_zero] at hreal
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at himag
  have him' := (le_abs_self (polePlanePhase D hh j x).im).trans himag
  have hd : (2 : ℝ)^(-258 : ℤ) * (|u| + ‖x‖^2) ≤
      (1 / 4 : ℝ) * (|u| + (2 : ℝ)^(-256 : ℤ) * ‖x‖^2) := by
    have hc : (2 : ℝ)^(-258 : ℤ) ≤ 1 / 4 := by norm_num
    have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg u)
    have he : (2 : ℝ)^(-258 : ℤ) = (1 / 4 : ℝ) * (2 : ℝ)^(-256 : ℤ) := by norm_num
    nlinarith only [hm, he]
  have hb := mul_le_mul_of_nonneg_left (add_le_add hreal (him.trans him'))
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hsum : (1 / 4 : ℝ) * (‖(u : ℂ) - polePlanePhase D hh j x‖ +
      ‖(u : ℂ) - polePlanePhase D hh j x‖) =
      (1 / 2 : ℝ) * ‖(u : ℂ) - polePlanePhase D hh j x‖ := by ring
  exact hd.trans ((hb.trans_eq hsum).trans hn)

#print axioms poleDenominator_real_lower

end Maxwell.Continuum.PeriodicBand
