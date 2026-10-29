import Maxwell.Continuum.PeriodicPerturbation

/-! Exact homogeneity of the actual compressed Maxwell velocity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicPerturbation

open FreeFiber ClusterComplement FiberAnalytic

theorem clusterVelocity_smul (c : ℂ) (t : Momentum) :
    clusterVelocity (c • t) = c • clusterVelocity t := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  funext ν
  change velocityBlock (c • t) ν (u ν) = c • velocityBlock t ν (u ν)
  have hd : bilinearDot (realMomentum (cornerSigns ν)) (c • t) =
      c * bilinearDot (realMomentum (cornerSigns ν)) t := by
    simp only [bilinearDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [velocityBlock_apply, velocityBlock_apply, hd, smul_smul]
  congr 1
  ring

theorem finiteVelocity_smul (c : ℂ) (t : Momentum) :
    finiteVelocity (c • t) = c • finiteVelocity t := by
  change compressionCLM (clusterVelocity (c • t)) = c • compressionCLM (clusterVelocity t)
  rw [clusterVelocity_smul, map_smul]

end Maxwell.Continuum.PeriodicPerturbation
