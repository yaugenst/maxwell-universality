import Maxwell.Continuum.FiberAnalyticInverse

/-!
# Polynomial dependence of the literal finite cluster blocks

Finite central blocks are assembled in the full alias operator norm. This
provides total formulas for both off-diagonal couplings, including complex
momenta where they are not adjoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberAnalytic

open FreeFiber ClusterComplement
open scoped Classical

theorem centralFamilyCLM_eq_boundedBlocks (F : Alias → PolarizationMap)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ ν, ‖F ν‖ ≤ C)
    (hzero : ∀ ν, ¬ IsCentralAlias ν → F ν = 0) :
    centralFamilyCLM (fun ν : CentralAlias => F ν.val) = boundedBlocks F hC hF := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  funext ν
  rw [centralFamilyCLM_apply]
  change centralBlockFamily _ ν (u ν) = F ν (u ν)
  by_cases hν : IsCentralAlias ν
  · rw [centralBlockFamily, dite_eq_left hν]
  · rw [centralBlockFamily, dite_eq_right hν, hzero ν hν]

theorem analyticAt_aliasCoordinate (z : Parameter) (ν : Alias) (j : Fin 3) :
    AnalyticAt ℂ (fun w : Parameter => aliasMomentum (scaledMomentum w.1) ν j) z :=
  (analyticAt_const.add (analyticAt_scaledCoordinate z j)).add analyticAt_const

theorem analyticAt_freeLeftBlock (z : Parameter) (ν : Alias) :
    AnalyticAt ℂ (fun w : Parameter => freeLeftCouplingBlock w.1 (totalEnergy w.2) ν) z :=
  (analyticAt_const.mul (analyticAt_block _ _ z (analyticAt_aliasCoordinate z ν)
    (analyticAt_totalEnergy z))).mul analyticAt_const

theorem analyticAt_freeRightBlock (z : Parameter) (ν : Alias) :
    AnalyticAt ℂ (fun w : Parameter => freeRightCouplingBlock w.1 (totalEnergy w.2) ν) z :=
  (analyticAt_const.mul (analyticAt_block _ _ z (analyticAt_aliasCoordinate z ν)
    (analyticAt_totalEnergy z))).mul analyticAt_const

def leftCouplingExtension (z : Parameter) : FiberMap :=
  centralFamilyCLM (fun ν => freeLeftCouplingBlock z.1 (totalEnergy z.2) ν.val) -
    (backgroundAmplitude : ℂ) • (clusterProjection * potential * complementProjection)

def rightCouplingExtension (z : Parameter) : FiberMap :=
  centralFamilyCLM (fun ν => freeRightCouplingBlock z.1 (totalEnergy z.2) ν.val) -
    (backgroundAmplitude : ℂ) • (complementProjection * potential * clusterProjection)

theorem leftCouplingExtension_eq (z : Parameter)
    (ht : ∀ j, ‖z.1 j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    leftCouplingExtension z = leftCoupling z.1 (totalEnergy z.2) ht := by
  unfold leftCouplingExtension leftCoupling freeLeftCoupling
  rw [centralFamilyCLM_eq_boundedBlocks _ (div_nonneg backgroundAmplitude_pos.le (by norm_num))
    (freeLeftCouplingBlock_norm_le z.1 (totalEnergy z.2) ht)]
  intro ν hν
  simp only [freeLeftCouplingBlock, clusterBlock_noncentral ν hν, zero_mul]

theorem rightCouplingExtension_eq (z : Parameter)
    (ht : ∀ j, ‖z.1 j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    rightCouplingExtension z = rightCoupling z.1 (totalEnergy z.2) ht := by
  unfold rightCouplingExtension rightCoupling freeRightCoupling
  rw [centralFamilyCLM_eq_boundedBlocks _ (div_nonneg backgroundAmplitude_pos.le (by norm_num))
    (freeRightCouplingBlock_norm_le z.1 (totalEnergy z.2) ht)]
  intro ν hν
  simp only [freeRightCouplingBlock, clusterBlock_noncentral ν hν, mul_zero]

theorem analyticAt_leftCouplingExtension (z : Parameter) :
    AnalyticAt ℂ leftCouplingExtension z := by
  have hf : AnalyticAt ℂ
      (fun w : Parameter => fun ν : CentralAlias => freeLeftCouplingBlock w.1 (totalEnergy w.2) ν.val) z :=
    AnalyticAt.pi (fun ν => analyticAt_freeLeftBlock z ν.val)
  exact (AnalyticAt.comp
    (f := fun w : Parameter => fun ν : CentralAlias => freeLeftCouplingBlock w.1 (totalEnergy w.2) ν.val)
    (centralFamilyCLM.analyticAt _) hf).sub analyticAt_const

theorem analyticAt_rightCouplingExtension (z : Parameter) :
    AnalyticAt ℂ rightCouplingExtension z := by
  have hf : AnalyticAt ℂ
      (fun w : Parameter => fun ν : CentralAlias => freeRightCouplingBlock w.1 (totalEnergy w.2) ν.val) z :=
    AnalyticAt.pi (fun ν => analyticAt_freeRightBlock z ν.val)
  exact (AnalyticAt.comp
    (f := fun w : Parameter => fun ν : CentralAlias => freeRightCouplingBlock w.1 (totalEnergy w.2) ν.val)
    (centralFamilyCLM.analyticAt _) hf).sub analyticAt_const

theorem directQuadratic_eq_centralFamily (t : Momentum) :
    directQuadratic t = centralFamilyCLM (fun ν : CentralAlias => quadraticBlock t ν.val) := by
  symm
  apply centralFamilyCLM_eq_boundedBlocks
  intro ν hν
  simp only [quadraticBlock, clusterBlock_noncentral ν hν, zero_mul]

theorem clusterVelocity_eq_centralFamily (t : Momentum) :
    clusterVelocity t = centralFamilyCLM (fun ν : CentralAlias => velocityBlock t ν.val) := by
  symm
  apply centralFamilyCLM_eq_boundedBlocks
  intro ν hν
  apply ContinuousLinearMap.ext
  intro u
  simp only [velocityBlock_apply, clusterBlock_noncentral ν hν, zero_apply, smul_zero]

theorem analyticAt_directQuadratic (z : Parameter) :
    AnalyticAt ℂ (fun w : Parameter => directQuadratic w.1) z := by
  have hf : AnalyticAt ℂ
      (fun w : Parameter => fun ν : CentralAlias => quadraticBlock w.1 ν.val) z := by
    apply AnalyticAt.pi
    intro ν
    exact (analyticAt_const.mul
      (analyticAt_block _ _ z (analyticAt_coordinate z) analyticAt_const)).mul analyticAt_const
  have h := AnalyticAt.comp
    (f := fun w : Parameter => fun ν : CentralAlias => quadraticBlock w.1 ν.val)
    (centralFamilyCLM.analyticAt _) hf
  simpa only [Function.comp_def, ← directQuadratic_eq_centralFamily] using h

theorem analyticAt_clusterVelocity (z : Parameter) :
    AnalyticAt ℂ (fun w : Parameter => clusterVelocity w.1) z := by
  have hf : AnalyticAt ℂ
      (fun w : Parameter => fun ν : CentralAlias => velocityBlock w.1 ν.val) z := by
    apply AnalyticAt.pi
    intro ν
    exact (analyticAt_const.mul
      (analyticAt_bilinearDot (realMomentum (cornerSigns ν.val)) _ z
        (analyticAt_coordinate z))).smul analyticAt_const
  have h := AnalyticAt.comp
    (f := fun w : Parameter => fun ν : CentralAlias => velocityBlock w.1 ν.val)
    (centralFamilyCLM.analyticAt _) hf
  simpa only [Function.comp_def, ← clusterVelocity_eq_centralFamily] using h

theorem analyticAt_leadingCluster (z : Parameter) :
    AnalyticAt ℂ (fun w : Parameter => leadingCluster w.1 w.2) z :=
  (analyticAt_const.add (analyticAt_clusterVelocity z)).sub
    (analyticAt_snd.smul analyticAt_const)

end Maxwell.Continuum.FiberAnalytic
