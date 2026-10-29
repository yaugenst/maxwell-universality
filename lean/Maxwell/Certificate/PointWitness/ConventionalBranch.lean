import Maxwell.Certificate.PointWitness.ConventionalCenter
import Maxwell.Spectral.CenteredFolding
import Maxwell.Spectral.BranchIdentification

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PeriodicYee
open scoped Topology
noncomputable section
set_option maxRecDepth 4000

private theorem spectral_data_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {T U : H →ₗ[ℂ] H} (hT : T.IsSymmetric) (hU : U.IsSymmetric) (h : T = U) :
    hT.eigenvalues rfl = hU.eigenvalues rfl ∧
      hT.eigenvectorBasis rfl = hU.eigenvectorBasis rfl := by
  subst U
  exact ⟨rfl, rfl⟩

private theorem euclidean_clm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v = M.toEuclideanLin v := rfl

/-- One full-cell analytic branch, with its eigenvector, projector and regular
resolvent. The vector is obtained from the same projector and is nonzero
near the center. -/
theorem exists_conventional_point_analytic_resolvent
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion) :
    ∃ value : ConventionalAnalytic.ComplexMomentum → ℂ,
    ∃ u : ConventionalAnalytic.ComplexMomentum → ConventionalPointSpace,
    ∃ P : ConventionalAnalytic.ComplexMomentum → ConventionalPointSpace →L[ℂ] ConventionalPointSpace,
    ∃ R : ConventionalAnalytic.ComplexMomentum × ℂ → ConventionalPointSpace →L[ℂ] ConventionalPointSpace,
      value 0 = (pointEnergy : ℂ) ∧ u 0 = conventionalPointVector hgap hexclude ∧
      P 0 = (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
        (conventionalPointVector hgap hexclude) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      AnalyticAt ℂ R (0, 0) ∧
      (∀ᶠ w in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum),
        u w ≠ 0 ∧ conventionalPointOperator w (u w) = value w • u w ∧
        P w * P w = P w ∧ conventionalPointOperator w * P w = value w • P w ∧
        P w * conventionalPointOperator w = value w • P w) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : ConventionalAnalytic.ComplexMomentum × ℂ),
        value z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible ∧
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).inverse =
          (value z.1 - ((pointEnergy : ℂ) + z.2))⁻¹ • P z.1 + R z) := by
  have hT : (conventionalPointOperator 0).toLinearMap.IsSymmetric := by
    rw [conventionalPointOperator_zero]
    exact conventionalPoint_symmetric
  have hm : (conventionalPointOperator 0).toLinearMap =
      conventionalPointFiber.toEuclideanLin := by
    rw [conventionalPointOperator_zero]
    rfl
  obtain ⟨hμ, hb⟩ := spectral_data_congr hT conventionalPoint_symmetric hm
  have hs (j : ConventionalPointIndex) (hj : j ≠ conventionalPointIndex hgap hexclude) :
      hT.eigenvalues rfl j ≠ hT.eigenvalues rfl (conventionalPointIndex hgap hexclude) := by
    simpa only [hμ] using conventionalPointIndex_simple hgap hexclude j hj
  have henergy : hT.eigenvalues rfl (conventionalPointIndex hgap hexclude) = pointEnergy := by
    simpa only [hμ] using conventionalPointIndex_energy hgap hexclude
  have hvector : hT.eigenvectorBasis rfl (conventionalPointIndex hgap hexclude) =
      conventionalPointVector hgap hexclude := by
    rw [hb]
    rfl
  obtain ⟨value, P, R, hv0, hP0, hv, hP, hR, hg, hr⟩ :=
    AnalyticEigenbranch.exists_analytic_resolvent_of_hermitian_simple
      conventionalPointOperator conventionalPointOperator_analytic hT
      (conventionalPointIndex hgap hexclude) hs
  rw [henergy] at hv0 hr
  rw [hvector] at hP0
  let u := fun w => P w (conventionalPointVector hgap hexclude)
  have hu : AnalyticAt ℂ u 0 :=
    ((ContinuousLinearMap.apply ℂ ConventionalPointSpace
      (conventionalPointVector hgap hexclude)).analyticAt (P 0)).comp hP
  have hu0 : u 0 = conventionalPointVector hgap hexclude := by
    simp only [u, hP0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [inner_self_eq_norm_sq_to_K, conventionalPointVector_norm]
    simp
  have hn : ∀ᶠ w in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum), u w ≠ 0 :=
    hu.continuousAt.eventually_ne (by
      rw [hu0]
      apply norm_ne_zero_iff.mp
      rw [conventionalPointVector_norm]
      norm_num)
  refine ⟨value, u, P, R, hv0, hu0, hP0, hv, hu, hP, hR, ?_, hr⟩
  filter_upwards [hg, hn] with w hw hnw
  refine ⟨hnw, ?_, hw⟩
  exact congrArg (fun T : ConventionalPointSpace →L[ℂ] ConventionalPointSpace =>
    T (conventionalPointVector hgap hexclude)) hw.2.1

def conventionalRealDisplacement (q : Momentum) : ConventionalAnalytic.ComplexMomentum :=
  ConventionalAnalytic.realMomentum ((2 * Real.pi) • q)

theorem conventionalRealDisplacement_tendsto :
    Filter.Tendsto conventionalRealDisplacement (𝓝 (0 : Momentum))
      (𝓝 (0 : ConventionalAnalytic.ComplexMomentum)) := by
  have hc : Continuous conventionalRealDisplacement := by
    unfold conventionalRealDisplacement ConventionalAnalytic.realMomentum
    fun_prop
  have hz : conventionalRealDisplacement 0 = 0 := by
    ext j
    simp [conventionalRealDisplacement, ConventionalAnalytic.realMomentum]
  simpa only [hz] using hc.continuousAt.tendsto (x := (0 : Momentum))

theorem conventionalPointOperator_real (q : Momentum) :
    conventionalPointOperator (conventionalRealDisplacement q) =
      Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
        (PeriodicYee.fiber Concrete.material (conventionalPointMomentum + (2 * Real.pi) • q)) := by
  unfold conventionalPointOperator conventionalRealDisplacement
  rw [show ConventionalAnalytic.realMomentum conventionalPointMomentum +
      ConventionalAnalytic.realMomentum ((2 * Real.pi) • q) =
      ConventionalAnalytic.realMomentum (conventionalPointMomentum + (2 * Real.pi) • q) by
    ext j; simp [ConventionalAnalytic.realMomentum]]
  exact ConventionalAnalytic.operator_real _ _

def centeredPointLift (q : Momentum) (v : PointSpace) : ConventionalPointSpace :=
  SectorSimplicity.liftedVector (Folding.centeredFoldingMatrix pointPrimitiveMomentum q) 0 v

theorem centeredPointLift_norm (q : Momentum) (v : PointSpace) :
    ‖centeredPointLift q v‖ = ‖v‖ := by
  let e := SectorSimplicity.matrixUnitaryEquiv
    (Folding.centeredFoldingMatrix pointPrimitiveMomentum q)
    (Folding.centeredFoldingMatrix_unitary pointPrimitiveMomentum q).1
    (Folding.centeredFoldingMatrix_unitary pointPrimitiveMomentum q).2
  change ‖e (SectorSimplicity.sectorEmbedding 0 v)‖ = ‖v‖
  rw [e.norm_map, SectorSimplicity.sectorEmbedding_norm]

theorem centeredPointLift_eigen (q : Momentum) (c : ℂ) (v : PointSpace)
    (hv : pointHolomorphicOperator (YeeAnalytic.realMomentum q) v = c • v) :
    conventionalPointOperator (conventionalRealDisplacement q) (centeredPointLift q v) =
      c • centeredPointLift q v := by
  have hp : (YeeTaylor.centeredFiber Concrete.material pointPrimitiveMomentum q).toEuclideanLin v =
      c • v := by
    rw [pointHolomorphicOperator, YeeAnalytic.holomorphicOperator_real] at hv
    simp only [YeeTaylor.shiftedCenteredOperator, Complex.ofReal_zero, zero_smul, sub_zero] at hv
    exact hv
  have hs := SectorSimplicity.sectorEmbedding_eigenvector
    (fun a => YeeTaylor.centeredFiber Concrete.material (Folding.sectorMomentum pointPrimitiveMomentum a) q)
    0 c v (by simpa only [pointSector_zero] using hp)
  have hm := congrArg (fun M : Matrix Electric20 (PrimitiveYee.Electric × Folding.Coset) ℂ =>
    M.toEuclideanLin (SectorSimplicity.sectorEmbedding 0 v))
    (Folding.centered_fiber_folding_intertwining Concrete.material Concrete.material_FCCPeriodic
      pointPrimitiveMomentum q)
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] at hm
  rw [conventionalPointOperator_real, euclidean_clm_apply]
  simp only [centeredPointLift, SectorSimplicity.liftedVector]
  simp only [conventionalPointMomentum, Matrix.toEuclideanLin] at hs ⊢
  rw [hm, hs, map_smul]

/-- The exact primitive branch and full conventional branch agree on nearby
physical momenta. The full resolvent excludes a distinct transported eigenvalue. -/
theorem conventional_point_branch_identification
    (fullValue primitiveValue : YeeAnalytic.ComplexMomentum → ℂ)
    (primitiveVector : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : ContinuousAt primitiveValue 0) (hv0 : primitiveValue 0 = (pointEnergy : ℂ))
    (hn : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), primitiveVector w ≠ 0)
    (he : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (primitiveVector w) = primitiveValue w • primitiveVector w)
    (hr : ∀ᶠ z in 𝓝 ((0, 0) : ConventionalAnalytic.ComplexMomentum × ℂ),
      fullValue z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible) :
    (fun q : Momentum => fullValue (conventionalRealDisplacement q)) =ᶠ[𝓝 0]
      fun q => primitiveValue (YeeAnalytic.realMomentum q) := by
  have hc : Continuous YeeAnalytic.realMomentum := by
    unfold YeeAnalytic.realMomentum
    fun_prop
  have ht : Filter.Tendsto YeeAnalytic.realMomentum (𝓝 (0 : Momentum))
      (𝓝 (0 : YeeAnalytic.ComplexMomentum)) := by
    simpa only [show YeeAnalytic.realMomentum 0 = 0 from rfl] using hc.continuousAt.tendsto (x := 0)
  apply BranchIdentification.eventuallyEq_of_offPole_invertible
    conventionalPointOperator fullValue conventionalRealDisplacement
    (fun q => primitiveValue (YeeAnalytic.realMomentum q)) 0 0 (pointEnergy : ℂ)
    conventionalRealDisplacement_tendsto
    (by simpa only [hv0, Function.comp_def] using hv.tendsto.comp ht) hr
  filter_upwards [ht.eventually hn, ht.eventually he] with q hneq heig
  refine ⟨centeredPointLift q (primitiveVector (YeeAnalytic.realMomentum q)), ?_,
    centeredPointLift_eigen q _ _ heig⟩
  intro hz
  have hh := centeredPointLift_norm q (primitiveVector (YeeAnalytic.realMomentum q))
  rw [hz, norm_zero] at hh
  exact hneq (norm_eq_zero.mp hh.symm)

/-- Evenness on real momenta is inherited by the very same conventional
branch identified above; it is not supplied as a symmetry premise. -/
theorem conventional_point_real_even_of_identification
    (fullValue primitiveValue : YeeAnalytic.ComplexMomentum → ℂ)
    (hid : (fun q : Momentum => fullValue (conventionalRealDisplacement q)) =ᶠ[𝓝 0]
      fun q => primitiveValue (YeeAnalytic.realMomentum q))
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), primitiveValue (-w) = primitiveValue w) :
    ∀ᶠ q : Momentum in 𝓝 0,
      fullValue (conventionalRealDisplacement (-q)) = fullValue (conventionalRealDisplacement q) := by
  have hc : Continuous YeeAnalytic.realMomentum := by
    unfold YeeAnalytic.realMomentum
    fun_prop
  have ht : Filter.Tendsto YeeAnalytic.realMomentum (𝓝 (0 : Momentum))
      (𝓝 (0 : YeeAnalytic.ComplexMomentum)) := by
    simpa only [show YeeAnalytic.realMomentum 0 = 0 from rfl] using hc.continuousAt.tendsto (x := 0)
  have hn : Filter.Tendsto (fun q : Momentum => -q) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousAt.tendsto (x := (0 : Momentum)))
  filter_upwards [hid, hn.eventually hid, ht.eventually heven] with q hq hneg he
  rw [hneg, hq]
  simpa only [show YeeAnalytic.realMomentum (-q) = -YeeAnalytic.realMomentum q by
    ext j; simp [YeeAnalytic.realMomentum]] using he

/-- The constructed conventional eigenvalue is real on physical momenta,
as a consequence of Hermiticity of the actual conventional Yee fiber. -/
theorem conventional_point_real_germ
    (value : ConventionalAnalytic.ComplexMomentum → ℂ)
    (u : ConventionalAnalytic.ComplexMomentum → ConventionalPointSpace)
    (hn : ∀ᶠ w in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum), u w ≠ 0)
    (he : ∀ᶠ w in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum),
      conventionalPointOperator w (u w) = value w • u w) :
    ∀ᶠ q : Momentum in 𝓝 0, (value (conventionalRealDisplacement q)).im = 0 := by
  filter_upwards [conventionalRealDisplacement_tendsto.eventually hn,
    conventionalRealDisplacement_tendsto.eventually he] with q hneq heig
  have hT : (conventionalPointOperator (conventionalRealDisplacement q)).toLinearMap.IsSymmetric := by
    rw [conventionalPointOperator_real]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (PeriodicYee.fiber_hermitian _ _)
  have hval : Module.End.HasEigenvalue
      (conventionalPointOperator (conventionalRealDisplacement q)).toLinearMap
      (value (conventionalRealDisplacement q)) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr heig, hneq⟩
  have hh := congrArg Complex.im (hT.conj_eigenvalue_eq_self hval)
  change -(value (conventionalRealDisplacement q)).im = (value (conventionalRealDisplacement q)).im at hh
  linarith

/-- Rescale the proved physical evenness to the standard real slice used by
the multivariable holomorphic identity theorem. -/
theorem conventional_point_standard_real_even
    (value : ConventionalAnalytic.ComplexMomentum → ℂ)
    (heven : ∀ᶠ q : Momentum in 𝓝 0,
      value (conventionalRealDisplacement (-q)) = value (conventionalRealDisplacement q)) :
    ∀ᶠ q : Momentum in 𝓝 0,
      value (-ConventionalAnalytic.realMomentum q) = value (ConventionalAnalytic.realMomentum q) := by
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hs (q : Momentum) : conventionalRealDisplacement ((2 * Real.pi)⁻¹ • q) =
      ConventionalAnalytic.realMomentum q := by
    unfold conventionalRealDisplacement
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
  have ht : Filter.Tendsto (fun q : Momentum => (2 * Real.pi)⁻¹ • q) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using
      ((continuous_const_smul (2 * Real.pi)⁻¹).continuousAt.tendsto (x := (0 : Momentum)))
  filter_upwards [ht.eventually heven] with q hq
  rw [← smul_neg, hs, hs] at hq
  simpa only [show ConventionalAnalytic.realMomentum (-q) = -ConventionalAnalytic.realMomentum q by
    ext j; simp [ConventionalAnalytic.realMomentum]] using hq

end
end Maxwell.Certificate.PointWitness
