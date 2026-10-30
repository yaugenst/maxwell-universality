import Maxwell.Continuum.CalibrationEdgeSymmetry

/-! Exact quantitative monotonicity in total physical energy, for the
actual calibration Schur complement including all longitudinal modes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped InnerProductSpace

theorem edgeEnergy_sub (e f : ℝ) :
    totalEnergy (f : ℂ)-totalEnergy (e : ℂ) = ((backgroundAmplitude*(f-e) : ℝ) : ℂ) := by
  simp only [totalEnergy, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

theorem edge_energy_step {e f : ℝ} (he : |e| ≤ 8) (hf : |f| ≤ 8) (hef : e ≤ f) :
    0 ≤ backgroundAmplitude*(f-e) ∧ backgroundAmplitude*(f-e) ≤ 1/4 := by
  have hdiff : f-e ≤ 16 := by have := (abs_le.mp hf).2; have := (abs_le.mp he).1; linarith
  refine ⟨mul_nonneg backgroundAmplitude_pos.le (sub_nonneg.mpr hef), ?_⟩
  have hm := mul_le_mul hdiff backgroundAmplitude_le backgroundAmplitude_pos.le (by norm_num : (0 : ℝ) ≤ 16)
  nlinarith only [hm]

theorem edgeSchur_form_difference (e f : ℝ) (he : |e| ≤ 8) (hf : |f| ≤ 8)
    (u : centralSpace) :
    (inner ℂ u (calibrationFiniteSchur 0 f edgeParameterBound (edgeEnergyBound hf) u)).re-
      (inner ℂ u (calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he) u)).re =
      -(backgroundAmplitude*(f-e)) *
        (inner ℂ (calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) u.val)
          (calibrationLift 0 f edgeParameterBound (edgeEnergyBound hf) u.val)).re := by
  let x : (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude).domain :=
    ⟨calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) u.val,
      calibrationLift_mem_domain _ _ _ _ u.val⟩
  let y : (materialFiber (scaledMomentum 0) (totalEnergy (f : ℂ)) backgroundAmplitude).domain :=
    ⟨calibrationLift 0 f edgeParameterBound (edgeEnergyBound hf) u.val,
      calibrationLift_mem_domain _ _ _ _ u.val⟩
  have hy := material_graph_energy_shift (scaledMomentum 0) (totalEnergy (f : ℂ))
    (totalEnergy (e : ℂ)) backgroundAmplitude y.val _ (LinearPMap.mem_graph _ y)
  rw [LinearPMap.mem_graph_iff] at hy
  obtain ⟨y', hy', hAy'⟩ := hy
  dsimp only at hy' hAy'
  have hs := edgeMaterial_formalAdjoint e x y'
  change inner ℂ (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude x)
    y'.val = inner ℂ x.val
      (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude y') at hs
  rw [hy', hAy', inner_add_right, inner_smul_right, edgeEnergy_sub] at hs
  dsimp only [x, y] at hs
  rw [calibrationLift_residual, calibrationLift_residual, calibrationSchur_inner_lift,
    calibrationLift_inner_schur] at hs
  have hr := congrArg Complex.re hs
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  have hsre := inner_re_symm (𝕜 := ℂ)
    (calibrationSchur 0 e edgeParameterBound (edgeEnergyBound he) u.val) u.val
  change (inner ℂ (calibrationSchur 0 e edgeParameterBound (edgeEnergyBound he) u.val) u.val).re =
    (inner ℂ u.val (calibrationSchur 0 e edgeParameterBound (edgeEnergyBound he) u.val)).re at hsre
  rw [hsre] at hr
  change (inner ℂ u.val (calibrationSchur 0 f edgeParameterBound (edgeEnergyBound hf) u.val)).re-
    (inner ℂ u.val (calibrationSchur 0 e edgeParameterBound (edgeEnergyBound he) u.val)).re = _
  linarith only [hr]

theorem edgeComplement_cross_nonneg (e f : ℝ) (he : |e| ≤ 8) (hf : |f| ≤ 8)
    (hef : e ≤ f) (v : FiberSpace) :
    0 ≤ (inner ℂ (calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he) v)
      (calibrationComplementInverse 0 f edgeParameterBound (edgeEnergyBound hf) v)).re := by
  let R := calibrationComplementInverse 0 (f : ℂ) edgeParameterBound (edgeEnergyBound hf)
  let x := calibrationComplementInverse 0 (e : ℂ) edgeParameterBound (edgeEnergyBound he) v
  let δ := backgroundAmplitude*(f-e)
  have hd := edge_energy_step he hf hef
  have hn : ‖R x‖ ≤ 2*‖x‖ := (calibrationComplementInverse_norm _ _ _ _ |> R.le_of_opNorm_le) x
  have hi : |(inner ℂ x (R x)).re| ≤ 2*‖x‖^2 := by
    apply ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans
    nlinarith only [mul_le_mul_of_nonneg_left hn (norm_nonneg x)]
  have hres := calibrationComplementInverse_resolvent 0 e f edgeParameterBound
    (edgeEnergyBound he) (edgeEnergyBound hf) v
  rw [edgeEnergy_sub] at hres
  have hval : R v = x+(δ : ℂ) • R x := by
    exact (sub_eq_iff_eq_add.mp hres).trans (add_comm _ _)
  change 0 ≤ (inner ℂ x (R v)).re
  rw [hval, inner_add_right, inner_smul_right, Complex.add_re,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 hd.1
  have hsmall := mul_le_mul_of_nonneg_right hd.2 (sq_nonneg ‖x‖)
  change 0 ≤ ‖x‖^2+δ*(inner ℂ x (R x)).re
  nlinarith only [hlow, hsmall, sq_nonneg ‖x‖]

theorem edgeLift_inner_bounds (e f : ℝ) (he : |e| ≤ 8) (hf : |f| ≤ 8)
    (hef : e ≤ f) (u : centralSpace) :
    ‖u‖^2 ≤ (inner ℂ (calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) u.val)
      (calibrationLift 0 f edgeParameterBound (edgeEnergyBound hf) u.val)).re ∧
    (inner ℂ (calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) u.val)
      (calibrationLift 0 f edgeParameterBound (edgeEnergyBound hf) u.val)).re ≤ 2*‖u‖^2 := by
  let v := calibrationRightCoupling u.val
  let x := calibrationComplementInverse 0 (e : ℂ) edgeParameterBound (edgeEnergyBound he) v
  let y := calibrationComplementInverse 0 (f : ℂ) edgeParameterBound (edgeEnergyBound hf) v
  have hPu := (mem_centralSpace_iff u.val).mp u.property
  have hux : inner ℂ u.val x = 0 := by
    rw [← hPu, central_inner, central_calibrationComplementInverse, inner_zero_right]
  have huy : inner ℂ u.val y = 0 := by
    rw [← hPu, central_inner, central_calibrationComplementInverse, inner_zero_right]
  have hxu : inner ℂ x u.val = 0 := by rw [← inner_conj_symm, hux, map_zero]
  have hx : ‖x‖ ≤ 14*backgroundAmplitude*‖u‖ := by
    apply ((calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he)).le_of_opNorm_le
      (calibrationComplementInverse_norm _ _ _ _) v).trans
    have hb := calibrationRightCoupling.le_of_opNorm_le calibrationRightCoupling_norm u.val
    change ‖v‖ ≤ 7*backgroundAmplitude*‖u‖ at hb
    linarith only [hb]
  have hy : ‖y‖ ≤ 14*backgroundAmplitude*‖u‖ := by
    apply ((calibrationComplementInverse 0 f edgeParameterBound (edgeEnergyBound hf)).le_of_opNorm_le
      (calibrationComplementInverse_norm _ _ _ _) v).trans
    have hb := calibrationRightCoupling.le_of_opNorm_le calibrationRightCoupling_norm u.val
    change ‖v‖ ≤ 7*backgroundAmplitude*‖u‖ at hb
    linarith only [hb]
  have hxy0 : 0 ≤ (inner ℂ x y).re := edgeComplement_cross_nonneg e f he hf hef v
  have hsmall : 14*backgroundAmplitude ≤ 1 := by nlinarith only [backgroundAmplitude_le]
  have hxy : (inner ℂ x y).re ≤ ‖u‖^2 := by
    apply (re_inner_le_norm (𝕜 := ℂ) x y).trans
    have hx' := hx.trans ((mul_le_mul_of_nonneg_right hsmall (norm_nonneg u)).trans_eq (one_mul _))
    have hy' := hy.trans ((mul_le_mul_of_nonneg_right hsmall (norm_nonneg u)).trans_eq (one_mul _))
    simpa only [pow_two] using mul_le_mul hx' hy' (norm_nonneg _) (norm_nonneg _)
  change ‖u‖^2 ≤ (inner ℂ (centralAliasProjection u.val-x) (centralAliasProjection u.val-y)).re ∧ _
  change _ ∧ (inner ℂ (centralAliasProjection u.val-x) (centralAliasProjection u.val-y)).re ≤ 2*‖u‖^2
  rw [hPu, inner_sub_left, inner_sub_right, inner_sub_right, huy, hxu,
    sub_zero, zero_sub, sub_neg_eq_add, Complex.add_re,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  change ‖u‖^2 ≤ ‖u‖^2+(inner ℂ x y).re ∧ ‖u‖^2+(inner ℂ x y).re ≤ 2*‖u‖^2
  constructor <;> linarith only [hxy0, hxy]

theorem edgeSchur_decrease (e f : ℝ) (he : |e| ≤ 8) (hf : |f| ≤ 8) (hef : e ≤ f)
    (u : centralSpace) :
    -2*(backgroundAmplitude*(f-e))*‖u‖^2 ≤
      (inner ℂ u (calibrationFiniteSchur 0 f edgeParameterBound (edgeEnergyBound hf) u)).re-
        (inner ℂ u (calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he) u)).re ∧
    (inner ℂ u (calibrationFiniteSchur 0 f edgeParameterBound (edgeEnergyBound hf) u)).re-
        (inner ℂ u (calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he) u)).re ≤
      -(backgroundAmplitude*(f-e))*‖u‖^2 := by
  rw [edgeSchur_form_difference e f he hf u]
  have hb := edgeLift_inner_bounds e f he hf hef u
  have hd := (edge_energy_step he hf hef).1
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hb.2 hd]
  · nlinarith only [mul_le_mul_of_nonneg_left hb.1 hd]

#print axioms edgeSchur_decrease

end Maxwell.Continuum.Calibration
