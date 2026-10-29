import Maxwell.Continuum.ClusterComplementExpansion

/-!
# Exact low block on the fixed transverse cluster

The direct compression is `ρ (K + Υ(t) - e P) + ρ² D(t)`.
Here `K` is the literal compressed nearest-neighbor potential and `D` is
the literal quadratic Maxwell block, whose norm is strictly below one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

def quadraticBlock (t : Momentum) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  clusterBlock ν * block t 0 * clusterBlock ν

theorem quadraticBlock_apply (t : Momentum) (ν : Alias) (v : Polarization) :
    quadraticBlock t ν v = clusterBlock ν (block t 0 (clusterBlock ν v)) := rfl

theorem block_zero_norm_le (t : Momentum) : ‖block t 0‖ ≤ 2 * ‖momentumVector t‖ ^ 2 := by
  have hb : block (0 : Momentum) 0 = 0 := by
    simp [block, blockMatrix, momentumSquare, momentumOuter, matrixCLM]
  have hv : momentumVector (0 : Momentum) = 0 := rfl
  simpa only [zero_add, hb, sub_zero, hv, norm_zero, mul_zero, zero_mul, zero_add] using
    block_variation_norm_le 0 t 0

theorem quadraticBlock_norm_le (t : Momentum) (ν : Alias) :
    ‖quadraticBlock t ν‖ ≤ 2 * ‖momentumVector t‖ ^ 2 :=
  (contraction_sandwich_norm_le _ _ _ (clusterBlock_norm_le ν) (clusterBlock_norm_le ν)).trans
    (block_zero_norm_le t)

def directQuadratic (t : Momentum) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (quadraticBlock t) (by positivity) (quadraticBlock_norm_le t)

theorem directQuadratic_norm_le (t : Momentum) :
    ‖directQuadratic t‖ ≤ 2 * ‖momentumVector t‖ ^ 2 := boundedBlocks_norm_le _ _ _

theorem directQuadratic_norm_lt_one (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : ‖directQuadratic t‖ < 1 := by
  have ht' := momentum_box_norm_le t ht
  nlinarith [directQuadratic_norm_le t, norm_nonneg (momentumVector t)]

def velocityBlock (t : Momentum) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  ((Real.pi : ℂ) * bilinearDot (realMomentum (cornerSigns ν)) t) • clusterBlock ν

theorem velocityBlock_apply (t : Momentum) (ν : Alias) (v : Polarization) :
    velocityBlock t ν v =
      ((Real.pi : ℂ) * bilinearDot (realMomentum (cornerSigns ν)) t) • clusterBlock ν v := rfl

theorem velocityBlock_norm_le (t : Momentum) (ν : Alias) :
    ‖velocityBlock t ν‖ ≤ 2 * Real.pi * ‖momentumVector t‖ := by
  by_cases hν : IsCentralAlias ν
  · have hs : ‖momentumVector (realMomentum (cornerSigns ν))‖ ≤ 2 := by
      nlinarith [cornerSigns_norm_sq ν hν, norm_nonneg (momentumVector (realMomentum (cornerSigns ν)))]
    have hdot := (bilinearDot_norm_le (realMomentum (cornerSigns ν)) t).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    rw [velocityBlock, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hdot Real.pi_pos.le)
      (clusterBlock_norm_le ν) (norm_nonneg _) (by positivity : 0 ≤ Real.pi * (2 * ‖momentumVector t‖))
    nlinarith
  · have hz : velocityBlock t ν = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      rw [velocityBlock_apply, clusterBlock_noncentral ν hν, zero_apply, smul_zero]
    rw [hz, norm_zero]
    positivity

def clusterVelocity (t : Momentum) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (velocityBlock t) (by positivity) (velocityBlock_norm_le t)

theorem clusterVelocity_norm_le (t : Momentum) :
    ‖clusterVelocity t‖ ≤ 2 * Real.pi * ‖momentumVector t‖ := boundedBlocks_norm_le _ _ _

def clusterPotential : FiberSpace →L[ℂ] FiberSpace :=
  -(clusterProjection * potential * clusterProjection)

def leadingCluster (t : Momentum) (e : ℂ) : FiberSpace →L[ℂ] FiberSpace :=
  clusterPotential + clusterVelocity t - e • clusterProjection

def lowBlock (t : Momentum) (e : ℂ) : FiberSpace →L[ℂ] FiberSpace :=
  (backgroundAmplitude : ℂ) • leadingCluster t e +
    (backgroundAmplitude : ℂ) ^ 2 • directQuadratic t

theorem cluster_free_block_expansion (t : Momentum) (e : ℂ) (ν : Alias) :
    clusterBlock ν * block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) * clusterBlock ν =
      (backgroundAmplitude : ℂ) • (velocityBlock t ν - e • clusterBlock ν) +
        (backgroundAmplitude : ℂ) ^ 2 • quadraticBlock t ν := by
  by_cases hν : IsCentralAlias ν
  · have hq : scaledMomentum t = (backgroundAmplitude : ℂ) • t := rfl
    have hc : 3 * ((Real.pi : ℂ) / 2) ^ 2 - totalEnergy e +
        2 * ((Real.pi : ℂ) / 2) * bilinearDot (realMomentum (cornerSigns ν)) (scaledMomentum t) =
        (backgroundAmplitude : ℂ) *
          ((Real.pi : ℂ) * bilinearDot (realMomentum (cornerSigns ν)) t - e) := by
      rw [hq, bilinearDot_smul_right, totalEnergy]
      push_cast
      ring
    rw [clusterBlock_central ν hν, central_momentum_decomposition,
      transverse_block_expansion _ _ _ _ (cornerSigns_norm_sq ν hν), hc, hq, block_smul_zero]
    apply ContinuousLinearMap.ext
    intro v
    change ((backgroundAmplitude : ℂ) *
        ((Real.pi : ℂ) * bilinearDot (realMomentum (cornerSigns ν)) t - e)) •
          ((1 - longitudinal (cornerSigns ν)) v) +
        (1 - longitudinal (cornerSigns ν))
          ((backgroundAmplitude : ℂ) ^ 2 • block t 0 ((1 - longitudinal (cornerSigns ν)) v)) = _
    rw [map_smul]
    change _ = (backgroundAmplitude : ℂ) •
      (velocityBlock t ν v - e • (1 - longitudinal (cornerSigns ν)) v) +
      (backgroundAmplitude : ℂ) ^ 2 • quadraticBlock t ν v
    rw [velocityBlock_apply, quadraticBlock_apply, clusterBlock_central ν hν]
    simp only [smul_sub, smul_smul, mul_sub, sub_smul]
  · apply ContinuousLinearMap.ext
    intro v
    change clusterBlock ν (block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)
      (clusterBlock ν v)) = (backgroundAmplitude : ℂ) •
      (velocityBlock t ν v - e • clusterBlock ν v) +
      (backgroundAmplitude : ℂ) ^ 2 • quadraticBlock t ν v
    rw [velocityBlock_apply, quadraticBlock_apply, clusterBlock_noncentral ν hν]
    simp only [zero_apply, smul_zero, sub_self, add_zero]

theorem cluster_free_compression (t : Momentum) (e : ℂ) (u : FiberSpace) :
    clusterProjection (operator (scaledMomentum t) (totalEnergy e)
      ⟨clusterProjection u, clusterProjection_mem_domain _ _ u⟩) =
      (backgroundAmplitude : ℂ) • (clusterVelocity t u - e • clusterProjection u) +
        (backgroundAmplitude : ℂ) ^ 2 • directQuadratic t u := by
  apply Subtype.ext
  funext ν
  exact congrArg (fun T : Polarization →L[ℂ] Polarization => T (u ν))
    (cluster_free_block_expansion t e ν)

theorem lowBlock_apply (t : Momentum) (e : ℂ) (u : FiberSpace) :
    lowBlock t e u = clusterProjection
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨clusterProjection u, clusterProjection_mem_domain _ _ u⟩) := by
  rw [materialFiber_apply, map_sub, map_smul, cluster_free_compression]
  change (backgroundAmplitude : ℂ) •
      (-(clusterProjection (potential (clusterProjection u))) + clusterVelocity t u -
        e • clusterProjection u) + (backgroundAmplitude : ℂ) ^ 2 • directQuadratic t u = _
  simp only [smul_sub, smul_add, smul_neg]
  abel

end Maxwell.Continuum.ClusterComplement
