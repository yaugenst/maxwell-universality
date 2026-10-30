import Maxwell.Continuum.CalibrationEdgeSplit

/-! A genuine negative gap on the 23-dimensional complement of the
actual corner top vector inside the full central calibration space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber ClusterComplement CornerBridge
open scoped InnerProductSpace

private theorem high_scalar {ρ e ell x y A : ℝ} (hρ : 0 ≤ ρ) (hρb : ρ ≤ 1/(2 : ℝ)^20)
    (he : -8 ≤ e) (hel : ell-e ≤ 1/100) (hA : 6 ≤ A) :
    -ρ*e*(x^2+y^2)-A*y^2+ρ*((ell-1/20)*x^2+14*x*y+7*y^2) ≤
      -ρ/40*(x^2+y^2) := by
  have hyoung : 14*x*y ≤ x^2/100+4900*y^2 := by
    nlinarith only [sq_nonneg (x/10-70*y)]
  have hxcoef : ρ*(ell-e-1/20+1/100) ≤ -ρ/40 := by
    have h := mul_le_mul_of_nonneg_left hel hρ
    nlinarith only [h, hρ]
  have hycoef : ρ*(4907-e)-A ≤ -ρ/40 := by
    have h := mul_le_mul_of_nonneg_left he hρ
    nlinarith only [h, hρb, hA]
  have hx' := mul_le_mul_of_nonneg_right hxcoef (sq_nonneg x)
  have hy' := mul_le_mul_of_nonneg_right hycoef (sq_nonneg y)
  have hcross := mul_le_mul_of_nonneg_left hyoung hρ
  nlinarith only [hx', hy', hcross]

theorem centralMaterial_form (e : ℝ) (u : centralSpace) :
    (inner ℂ u.val (calibrationCentralMaterial 0 e u.val)).re =
      -backgroundAmplitude*e*‖u‖^2-(3*Real.pi^2/4)*‖u.val-clusterProjection u.val‖^2-
        backgroundAmplitude*(inner ℂ u.val (potential u.val)).re := by
  have hPu := (mem_centralSpace_iff u.val).mp u.property
  change (inner ℂ u.val (centralFree 0 e u.val-(backgroundAmplitude : ℂ) •
    centralAliasProjection (potential (centralAliasProjection u.val)))).re = _
  rw [hPu, inner_sub_right, inner_smul_right, ← central_inner, hPu, Complex.sub_re,
    centralFree_form]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem centralMaterial_top_high (e : ℝ) (he : |e| ≤ 8)
    (hel : |e-Corner.lambdaStar| ≤ 1/100)
    (u : centralSpace) (hu : inner ℂ topState.val u.val = 0) :
    (inner ℂ u.val (calibrationCentralMaterial 0 e u.val)).re ≤
      -backgroundAmplitude/40*‖u‖^2 := by
  let x := clusterProjection u.val
  let y := u.val-clusterProjection u.val
  have hsum : x+y = u.val := add_sub_cancel _ _
  have hpot := potential_split_lower x y
  rw [hsum] at hpot
  have hgap := central_cluster_top_gap u hu
  have hpot' : -(inner ℂ u.val (potential u.val)).re ≤
      (Corner.lambdaStar-1/20)*‖x‖^2+14*‖x‖*‖y‖+7*‖y‖^2 := by
    change -(inner ℂ x (potential x)).re ≤ (Corner.lambdaStar-1/20)*‖x‖^2 at hgap
    linarith only [hpot, hgap]
  have hρ : backgroundAmplitude ≤ 1/(2 : ℝ)^20 := by norm_num [backgroundAmplitude]
  have hbase : (6 : ℝ) ≤ 3*Real.pi^2/4 := by nlinarith only [Real.pi_gt_three]
  have hnum := high_scalar backgroundAmplitude_pos.le hρ (abs_le.mp he).1
    (show Corner.lambdaStar-e ≤ 1/100 by linarith only [(abs_le.mp hel).1]) hbase
    (x := ‖x‖) (y := ‖y‖)
  have hsplit : ‖u‖^2 = ‖x‖^2+‖y‖^2 := cluster_norm_split u.val
  rw [centralMaterial_form, hsplit]
  have hp := mul_le_mul_of_nonneg_left hpot' backgroundAmplitude_pos.le
  change -backgroundAmplitude*e*(‖x‖^2+‖y‖^2)-(3*Real.pi^2/4)*‖y‖^2-
    backgroundAmplitude*(inner ℂ u.val (potential u.val)).re ≤ _
  linarith only [hp, hnum]

theorem calibrationSchur_correction_norm (e : ℝ) (he : |e| ≤ 8) :
    ‖calibrationLeftCoupling*calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he)*
      calibrationRightCoupling‖ ≤ 98*backgroundAmplitude^2 := by
  have hL := calibrationLeftCoupling_norm
  have hR := calibrationComplementInverse_norm 0 e edgeParameterBound (edgeEnergyBound he)
  have hB := calibrationRightCoupling_norm
  have hρ0 := backgroundAmplitude_pos.le
  calc
    _ ≤ (‖calibrationLeftCoupling‖*‖calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he)‖)*
        ‖calibrationRightCoupling‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((7*backgroundAmplitude)*2)*(7*backgroundAmplitude) :=
      mul_le_mul (mul_le_mul hL hR (norm_nonneg _) (by positivity)) hB (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem edgeSchur_top_high (e : ℝ) (he : |e| ≤ 8)
    (hel : |e-Corner.lambdaStar| ≤ 1/100)
    (u : centralSpace) (hu : inner ℂ topState.val u.val = 0) :
    (inner ℂ u (calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he) u)).re ≤
      -backgroundAmplitude/100*‖u‖^2 := by
  let T := calibrationLeftCoupling*
    calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he)*calibrationRightCoupling
  have ht : ‖T‖ ≤ 98*backgroundAmplitude^2 := calibrationSchur_correction_norm e he
  have hi : |(inner ℂ u.val (T u.val)).re| ≤ 98*backgroundAmplitude^2*‖u‖^2 := by
    apply ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans
    change ‖u‖*‖T u.val‖ ≤ _
    have h := T.le_of_opNorm_le ht u.val
    change ‖T u.val‖ ≤ 98*backgroundAmplitude^2*‖u‖ at h
    nlinarith only [mul_le_mul_of_nonneg_left h (norm_nonneg u)]
  have hc : 98*backgroundAmplitude^2 ≤ backgroundAmplitude/200 := by
    have h : backgroundAmplitude ≤ 1/(2 : ℝ)^20 := by norm_num [backgroundAmplitude]
    have hm := mul_le_mul_of_nonneg_left h backgroundAmplitude_pos.le
    nlinarith only [hm, backgroundAmplitude_pos]
  have hg := centralMaterial_top_high e he hel u hu
  change (inner ℂ u.val (calibrationCentralMaterial 0 e u.val-T u.val)).re ≤ _
  rw [inner_sub_right, Complex.sub_re]
  have hec := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖)
  have hl := (abs_le.mp hi).1
  nlinarith only [hg, hec, hl, mul_nonneg backgroundAmplitude_pos.le (sq_nonneg ‖u‖)]

#print axioms edgeSchur_top_high

end Maxwell.Continuum.Calibration
