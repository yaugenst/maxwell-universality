import Maxwell.Certificate.PointWitness.EvenAnalyticBranch
import Maxwell.Spectral.SectorSimplicity
import Maxwell.Spectral.ConventionalAnalytic

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PeriodicYee
noncomputable section

abbrev ConventionalPointSpace := EuclideanSpace ℂ Electric20
abbrev ConventionalPointIndex := Fin (Module.finrank ℂ ConventionalPointSpace)

def pointPrimitiveMomentum : Momentum := PrimitiveYee.timeReversalMomentum ![1,1,0]

def conventionalPointMomentum : Momentum := Folding.conventionalMomentum pointPrimitiveMomentum

def conventionalPointFiber : Matrix Electric20 Electric20 ℂ :=
  PeriodicYee.fiber Concrete.material conventionalPointMomentum

def conventionalPointOperator (z : ConventionalAnalytic.ComplexMomentum) :
    ConventionalPointSpace →L[ℂ] ConventionalPointSpace :=
  ConventionalAnalytic.operator Concrete.material
    (ConventionalAnalytic.realMomentum conventionalPointMomentum + z)

theorem conventionalPointOperator_zero : conventionalPointOperator 0 =
    Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ) conventionalPointFiber := by
  simp only [conventionalPointOperator, add_zero, ConventionalAnalytic.operator_real,
    conventionalPointFiber]

theorem conventionalPointOperator_analytic : AnalyticAt ℂ conventionalPointOperator 0 := by
  exact (ConventionalAnalytic.operator_analyticAt _ _).comp
    (analyticAt_const.add analyticAt_id)

theorem conventionalPoint_symmetric : conventionalPointFiber.toEuclideanLin.IsSymmetric :=
  SectorSimplicity.conventional_symmetric pointPrimitiveMomentum

theorem pointSector_zero : Folding.sectorMomentum pointPrimitiveMomentum 0 =
    pointPrimitiveMomentum := by
  ext j
  fin_cases j <;> simp [Folding.sectorMomentum, Folding.sectorTranslation,
    PrimitiveYee.timeReversalMomentum]

/-- The unresolved finite input: none of the other three actual primitive
sectors has the selected energy. It is independent of the two-band gap in
the selected sector. -/
def PointOtherSectorExclusion : Prop :=
  ∀ b : Folding.Coset, b ≠ 0 → ∀ j,
    (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum b).eigenvalues rfl j ≠
      pointEnergy

private theorem eigenvalues_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {T U : H →ₗ[ℂ] H} (hT : T.IsSymmetric) (hU : U.IsSymmetric) (h : T = U) :
    hT.eigenvalues rfl = hU.eigenvalues rfl := by
  subst U
  rfl

set_option maxHeartbeats 800000 in
theorem conventionalPoint_simple_exists (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    Module.finrank ℂ (Module.End.eigenspace conventionalPointFiber.toEuclideanLin
      (pointEnergy : ℂ)) = 1 ∧
    ∃ j : ConventionalPointIndex,
      conventionalPoint_symmetric.eigenvalues rfl j = pointEnergy ∧
      ∀ l, l ≠ j → conventionalPoint_symmetric.eigenvalues rfl l ≠
        conventionalPoint_symmetric.eigenvalues rfl j := by
  have hm : (PrimitiveYee.fiber Concrete.material
      (Folding.sectorMomentum pointPrimitiveMomentum 0)).toEuclideanLin = pointOperator := by
    rw [pointSector_zero]
    rfl
  have hμ : (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum 0).eigenvalues rfl =
      pointOperator_symmetric.eigenvalues rfl := eigenvalues_congr _ _ hm
  have hs (j : PointIndex) (hj : j ≠ pointIndex0) :
      (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum 0).eigenvalues rfl j ≠
        (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum 0).eigenvalues rfl pointIndex0 := by
    simpa only [hμ] using pointIndex0_simple hgap j hj
  have he (b : Folding.Coset) (hb : b ≠ 0) (j : PointIndex) :
      (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum b).eigenvalues rfl j ≠
        (SectorSimplicity.primitive_symmetric pointPrimitiveMomentum 0).eigenvalues rfl pointIndex0 := by
    simpa only [hμ, pointEnergy] using hexclude b hb j
  obtain ⟨_, _, hd, hi⟩ := SectorSimplicity.concrete_folding_simple
    pointPrimitiveMomentum 0 pointIndex0 hs he
  rw [hμ] at hd hi
  exact ⟨hd, hi⟩

def conventionalPointIndex (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) : ConventionalPointIndex :=
  Classical.choose (conventionalPoint_simple_exists hgap hexclude).2

theorem conventionalPointIndex_energy (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    conventionalPoint_symmetric.eigenvalues rfl (conventionalPointIndex hgap hexclude) =
      pointEnergy :=
  (Classical.choose_spec (conventionalPoint_simple_exists hgap hexclude).2).1

theorem conventionalPointIndex_simple (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) (j : ConventionalPointIndex)
    (hj : j ≠ conventionalPointIndex hgap hexclude) :
    conventionalPoint_symmetric.eigenvalues rfl j ≠
      conventionalPoint_symmetric.eigenvalues rfl (conventionalPointIndex hgap hexclude) :=
  (Classical.choose_spec (conventionalPoint_simple_exists hgap hexclude).2).2 j hj

def conventionalPointVector (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) : ConventionalPointSpace :=
  conventionalPoint_symmetric.eigenvectorBasis rfl (conventionalPointIndex hgap hexclude)

theorem conventionalPointVector_norm (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) : ‖conventionalPointVector hgap hexclude‖ = 1 :=
  (conventionalPoint_symmetric.eigenvectorBasis rfl).norm_eq_one _

theorem conventionalPointVector_eigen (hgap : PointClusterComplementGap)
    (hexclude : PointOtherSectorExclusion) :
    conventionalPointFiber.toEuclideanLin (conventionalPointVector hgap hexclude) =
      (pointEnergy : ℂ) • conventionalPointVector hgap hexclude := by
  simpa only [conventionalPointVector, RCLike.ofReal_eq_complex_ofReal,
    conventionalPointIndex_energy] using
    conventionalPoint_symmetric.apply_eigenvectorBasis rfl (conventionalPointIndex hgap hexclude)

end
end Maxwell.Certificate.PointWitness
