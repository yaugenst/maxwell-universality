import Maxwell.Continuum.CalibrationEdgeMonotone
import Maxwell.Continuum.CornerBridgeGap

/-! Exact transverse/longitudinal decomposition inside the calibration
central space. The longitudinal coordinates remain present throughout. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber ClusterComplement PeriodicPerturbation CornerBridge
open scoped InnerProductSpace

theorem central_cluster_projection (u : FiberSpace) :
    centralAliasProjection (clusterProjection u) = clusterProjection u := by
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  by_cases hν : IsCentralAlias ν
  · rw [ite_eq_left hν]
  · simp only [hν, ↓reduceIte, clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply]

theorem cluster_central_projection (u : FiberSpace) :
    clusterProjection (centralAliasProjection u) = clusterProjection u := by
  apply Subtype.ext
  funext ν
  rw [clusterProjection_apply, centralAliasProjection_apply]
  by_cases hν : IsCentralAlias ν
  · rw [ite_eq_left hν]
    rfl
  · simp only [hν, ↓reduceIte, clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply]

theorem cluster_inner (u v : FiberSpace) :
    inner ℂ (clusterProjection u) v = inner ℂ u (clusterProjection v) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    clusterProjection_isStarProjection.isSelfAdjoint) u v

theorem cluster_longitudinal_orthogonal (u : FiberSpace) :
    inner ℂ (clusterProjection u) (u-clusterProjection u) = 0 := by
  rw [cluster_inner, map_sub, clusterProjection_idempotent, sub_self, inner_zero_right]

theorem cluster_norm_split (u : FiberSpace) :
    ‖u‖^2 = ‖clusterProjection u‖^2+‖u-clusterProjection u‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (clusterProjection u) (u-clusterProjection u) (cluster_longitudinal_orthogonal u)
  simpa only [add_sub_cancel, pow_two] using h

theorem centralFree_zero_momentum (e : ℂ) (u : centralSpace) :
    centralFree 0 e u.val = (-(backgroundAmplitude : ℂ)*e) • u.val-
      ((3*Real.pi^2/4 : ℝ) : ℂ) • (u.val-clusterProjection u.val) := by
  have hzero : scaledMomentum (0 : Momentum) = 0 := by
    funext j
    simp only [scaledMomentum, Pi.zero_apply, mul_zero]
  have hbase : 3*((Real.pi : ℂ)/2)^2 = ((3*Real.pi^2/4 : ℝ) : ℂ) := by push_cast; ring
  apply Subtype.ext
  funext ν
  change centralFreeBlock 0 e ν (u.val ν) =
    (-(backgroundAmplitude : ℂ)*e) • (u.val ν)-
      ((3*Real.pi^2/4 : ℝ) : ℂ) • (u.val ν-clusterProjection u.val ν)
  by_cases hν : IsCentralAlias ν
  · rw [centralFreeBlock, ite_eq_left hν, hzero, central_momentum_decomposition, add_zero,
      block_corner _ _ _ (cornerSigns_norm_sq ν hν), hbase,
      clusterProjection_apply, clusterBlock_central ν hν]
    simp only [sub_apply, smul_apply]
    change (((3*Real.pi^2/4 : ℝ) : ℂ)-totalEnergy e) • u.val ν-
      ((3*Real.pi^2/4 : ℝ) : ℂ) • longitudinal (cornerSigns ν) (u.val ν) =
      (-(backgroundAmplitude : ℂ)*e) • u.val ν-
        ((3*Real.pi^2/4 : ℝ) : ℂ) • (u.val ν-(u.val ν-longitudinal (cornerSigns ν) (u.val ν)))
    rw [sub_sub_cancel]
    have he : ((3*Real.pi^2/4 : ℝ) : ℂ)-totalEnergy e = -(backgroundAmplitude : ℂ)*e := by
      unfold totalEnergy
      ring
    rw [he]
  · rw [centralFreeBlock, ite_eq_right hν, zero_apply, centralSpace_noncentral u ν hν,
      clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply]
    simp only [smul_zero, sub_self]

theorem centralFree_form (e : ℝ) (u : centralSpace) :
    (inner ℂ u.val (centralFree 0 e u.val)).re =
      -backgroundAmplitude*e*‖u‖^2-(3*Real.pi^2/4)*‖u.val-clusterProjection u.val‖^2 := by
  let y := u.val-clusterProjection u.val
  have hinner : inner ℂ u.val y = inner ℂ y y := by
    have h := inner_add_left (𝕜 := ℂ) (clusterProjection u.val) y y
    rw [show clusterProjection u.val+y = u.val from add_sub_cancel _ _,
      cluster_longitudinal_orthogonal, zero_add] at h
    exact h
  rw [centralFree_zero_momentum, inner_sub_right, inner_smul_right, inner_smul_right, hinner]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_pow]
  change ((-(backgroundAmplitude : ℂ)*(e : ℂ))*((‖u‖^2 : ℝ) : ℂ)-
    ((3*Real.pi^2/4 : ℝ) : ℂ)*((‖y‖^2 : ℝ) : ℂ)).re = _
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, mul_zero, sub_zero]
  rfl

theorem potential_re_bound (x y : FiberSpace) :
    |(inner ℂ x (potential y)).re| ≤ 7*‖x‖*‖y‖ := by
  apply ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)).trans
  have h := potential.le_of_opNorm_le potential_norm_le y
  nlinarith only [mul_le_mul_of_nonneg_left h (norm_nonneg x)]

theorem potential_split_lower (x y : FiberSpace) :
    -(inner ℂ (x+y) (potential (x+y))).re ≤
      -(inner ℂ x (potential x)).re+14*‖x‖*‖y‖+7*‖y‖^2 := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  simp only [Complex.add_re]
  have hxy := (abs_le.mp (potential_re_bound x y)).1
  have hyx := (abs_le.mp (potential_re_bound y x)).1
  have hyy := (abs_le.mp (potential_re_bound y y)).1
  nlinarith only [hxy, hyx, hyy]

theorem central_cluster_top_gap (u : centralSpace) (hu : inner ℂ topState.val u.val = 0) :
    -(inner ℂ (clusterProjection u.val) (potential (clusterProjection u.val))).re ≤
      (Corner.lambdaStar-1/20)*‖clusterProjection u.val‖^2 := by
  let x : clusterSpace := ⟨clusterProjection u.val, ⟨u.val, rfl⟩⟩
  have hPx := (mem_clusterSpace_iff x.val).mp x.property
  have hx : inner ℂ topState x = 0 := by
    change inner ℂ topState.val (clusterProjection u.val) = 0
    rw [← cluster_inner, (mem_clusterSpace_iff topState.val).mp topState.property]
    exact hu
  have hg := finiteK_gap x hx
  have hform : inner ℂ x (finiteK x) = -inner ℂ x.val (potential x.val) := by
    change inner ℂ x.val (finiteK x).val = _
    rw [finiteK_apply]
    change inner ℂ x.val (-(clusterProjection (potential (clusterProjection x.val)))) = _
    rw [hPx, inner_neg_right, ← cluster_inner, hPx]
  rw [inner_sub_right, inner_smul_right x x (Corner.lambdaStar : ℂ), hform, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow] at hg
  change (1/20 : ℝ)*‖x‖^2 ≤
    (((Corner.lambdaStar : ℂ)*((‖x‖^2 : ℝ) : ℂ))- -inner ℂ x.val (potential x.val)).re at hg
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hg
  change (1/20 : ℝ)*‖clusterProjection u.val‖^2 ≤
    Corner.lambdaStar*‖clusterProjection u.val‖^2 -
      -(inner ℂ (clusterProjection u.val) (potential (clusterProjection u.val))).re at hg
  linarith only [hg]

#print axioms centralFree_zero_momentum
#print axioms central_cluster_top_gap

end Maxwell.Continuum.Calibration
