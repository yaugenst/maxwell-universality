import Maxwell.Continuum.CornerBridgeHessian

/-! The actual directional corner quadratic form, including the physical π factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement PeriodicPerturbation
open scoped InnerProductSpace

def physicalHighVelocity (t : Corner.Vec) : RankOneBand.highSpace topState :=
  ∑ j : Fin 3, ((Real.pi * t j : ℝ) : ℂ) • highVelocity j

def cornerQuadratic (t : Corner.Vec) : ℝ :=
  Real.pi ^ 2 * ∑ j : Fin 3, Corner.hessianCoefficient j * (t j)^2

theorem physicalHighVelocity_eq_projection (t : Corner.Vec) :
    physicalHighVelocity t = RankOneBand.project topState (finiteVelocity (realMomentum t) topState) := by
  rw [finiteVelocity_topState,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  have hj : RankOneBand.project topState (velocityState j) = highVelocity j :=
    RankOneBand.project_embed (highVelocity j)
  rw [hj]
  congr 1
  exact Complex.ofReal_mul _ _

/-- The exact quadratic form of the actual complementary inverse. -/
theorem physicalHighVelocity_quadratic (t : Corner.Vec) :
    inner ℂ (physicalHighVelocity t) (actualCornerData.baseInverse (physicalHighVelocity t)) =
      (cornerQuadratic t : ℂ) := by
  rw [physicalHighVelocity,map_sum,sum_inner]
  simp_rw [inner_sum,map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal,
    baseInverse_velocity_gram,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  unfold cornerQuadratic
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cornerQuadratic_bounds (t : Corner.Vec) :
    (Real.pi ^ 2 / 14) * dotProduct t t ≤ cornerQuadratic t ∧
      cornerQuadratic t ≤ (20 * Real.pi ^ 2) * dotProduct t t := by
  have hlo : (1 / 14 : ℝ) * ∑ j, (t j)^2 ≤
      ∑ j, Corner.hessianCoefficient j * (t j)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (Corner.hessianCoefficient_bounds j).1 (sq_nonneg _)
  have hhi : (∑ j, Corner.hessianCoefficient j * (t j)^2) ≤ 20 * ∑ j, (t j)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (Corner.hessianCoefficient_bounds j).2 (sq_nonneg _)
  have hn : dotProduct t t = ∑ j, (t j)^2 := by simp only [dotProduct,pow_two]
  rw [cornerQuadratic,hn]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg Real.pi)]
  · nlinarith [mul_le_mul_of_nonneg_left hhi (sq_nonneg Real.pi)]

theorem clusterVelocity_real_isSymmetric (t : Corner.Vec) :
    (clusterVelocity (realMomentum t)).IsSymmetric := by
  intro u v
  change inner ℂ (clusterVelocity (realMomentum t) u) v =
    inner ℂ u (clusterVelocity (realMomentum t) v)
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro ν
  change inner ℂ (velocityBlock (realMomentum t) ν (u ν)) (v ν) =
    inner ℂ (u ν) (velocityBlock (realMomentum t) ν (v ν))
  have hc : (Real.pi : ℂ) * bilinearDot (realMomentum (cornerSigns ν)) (realMomentum t) =
      ((Real.pi * ∑ j, cornerSigns ν j * t j : ℝ) : ℂ) := by
    simp only [bilinearDot,realMomentum,Complex.ofReal_mul,Complex.ofReal_sum]
  rw [velocityBlock_apply,velocityBlock_apply,hc,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  congr 1
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (clusterBlock_isStarProjection ν).isSelfAdjoint) (u ν) (v ν)

theorem finiteVelocity_real_isSymmetric (t : Corner.Vec) :
    (finiteVelocity (realMomentum t)).IsSymmetric := by
  intro u v
  change inner ℂ (clusterProjection (clusterVelocity (realMomentum t) u.val)) v.val =
    inner ℂ u.val (clusterProjection (clusterVelocity (realMomentum t) v.val))
  rw [clusterProjection_clusterVelocity,clusterProjection_clusterVelocity]
  exact clusterVelocity_real_isSymmetric t u.val v.val

/-- Direct interface for the affine simple-eigenvalue second derivative theorem. -/
theorem affineCoefficient_identity (t : Corner.Vec) :
    inner ℂ topState (finiteVelocity (realMomentum t)
      (RankOneBand.embed topState (actualCornerData.baseInverse
        (RankOneBand.project topState (finiteVelocity (realMomentum t) topState))))) =
      (cornerQuadratic t : ℂ) := by
  have hs (u v : clusterSpace) :
      inner ℂ (finiteVelocity (realMomentum t) u) v =
        inner ℂ u (finiteVelocity (realMomentum t) v) :=
    finiteVelocity_real_isSymmetric t u v
  rw [← hs,← physicalHighVelocity_eq_projection]
  have hv : finiteVelocity (realMomentum t) topState =
      RankOneBand.embed topState (physicalHighVelocity t) := by
    rw [physicalHighVelocity_eq_projection,actualCornerData.embed_project]
    change _ = _ - (inner ℂ topState (finiteVelocity (realMomentum t) topState)) • topState
    rw [topState_velocity_mean,zero_smul,sub_zero]
  rw [hv]
  exact physicalHighVelocity_quadratic t

end Maxwell.Continuum.CornerBridge
