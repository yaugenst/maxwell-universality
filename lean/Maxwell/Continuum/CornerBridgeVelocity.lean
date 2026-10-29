import Maxwell.Continuum.CornerBridgeTop

/-! Exact velocity action and zero linear energy shift at the actual top state. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement PeriodicPerturbation
open scoped InnerProductSpace

theorem clusterVelocity_packReal (t : Momentum) (u : Corner.ClusterField)
    (hu : Corner.clusterProjection u = u) :
    clusterVelocity t (packReal u) =
      ∑ j : Fin 3, ((Real.pi : ℂ) * t j) • packReal (Corner.velocity j u) := by
  have hpu : clusterProjection (packReal u) = packReal u := by
    rw [clusterProjection_packReal,hu]
  apply eq_of_aliases
  · intro ν hν
    change velocityBlock t ν (packReal u ν) = 0
    rw [velocityBlock_apply,clusterBlock_noncentral ν hν,zero_apply,smul_zero]
  · intro ν hν
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply]
    simp only [packReal,pack_noncentral _ ν hν,smul_zero,Finset.sum_const_zero]
  · intro s
    have hp : clusterBlock (cubeAlias s) (packReal u (cubeAlias s)) =
        packReal u (cubeAlias s) := congrArg (fun x : FiberSpace => x (cubeAlias s)) hpu
    change velocityBlock t (cubeAlias s) (packReal u (cubeAlias s)) = _
    rw [velocityBlock_apply,hp,alias_signs]
    apply PiLp.ext
    intro i
    simp only [packReal,pack_alias,realCube,realMomentum,momentumVector,Corner.velocity,
      lp.coeFn_sum,WithLp.ofLp_sum,WithLp.ofLp_smul,
      Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,bilinearDot,
      Complex.ofReal_mul,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem topState_velocity_mean (t : Momentum) :
    inner ℂ topState (finiteVelocity t topState) = 0 := by
  change inner ℂ topState.val
    (clusterProjection (clusterVelocity t topState.val)) = 0
  rw [clusterProjection_clusterVelocity]
  change inner ℂ (packReal Corner.normalizedClusterVector)
    (clusterVelocity t (packReal Corner.normalizedClusterVector)) = 0
  rw [clusterVelocity_packReal t _ normalizedCorner_transverse,inner_sum]
  simp only [inner_smul_right,packReal_inner,Corner.normalized_velocity_mean,
    Complex.ofReal_zero,mul_zero,Finset.sum_const_zero]

end Maxwell.Continuum.CornerBridge
