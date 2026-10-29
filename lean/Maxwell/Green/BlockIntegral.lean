import Maxwell.Green.SourceProfile
import Maxwell.Green.CompressedReadout
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Actual operator-valued Bloch integral for a translated weighted defect
block. Quadratic identities determine the whole complex-linear operator. -/
namespace Maxwell.Green.SourceProfile

open MeasureTheory Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.BlochResolvent Maxwell.Green.PhysicalCompression
open scoped Matrix.Norms.Elementwise
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {N : ℕ}

def torusSourceMatrix (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (t : Torus) :
    Matrix Edge20 (Fin N) ℂ := fun r i =>
  if r = (edgeCellEquiv (edges i)).1 then
    (Real.sqrt (W i : ℝ) : ℂ) * UnitAddTorus.mFourier (-(edgeCellEquiv (edges i)).2) t else 0

def torusSource (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (t : Torus) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ Edge20 :=
  rectangularMap (torusSourceMatrix edges W t)

theorem torusSourceMatrix_continuous (edges : Fin N ↪ Edge) (W : Fin N → ℚ) :
    Continuous (torusSourceMatrix edges W) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro i
  unfold torusSourceMatrix
  split_ifs
  · exact continuous_const.mul (UnitAddTorus.mFourier _).continuous
  · exact continuous_const

theorem torusSource_continuous (edges : Fin N ↪ Edge) (W : Fin N → ℚ) :
    Continuous (torusSource edges W) :=
  rectangularMap.continuous.comp (torusSourceMatrix_continuous edges W)

theorem torusSource_angular (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (q : Fin 3 → ℝ) :
    torusSource edges W (angularTorusPoint q) = sourceRight edges W (realMomentum q) := by
  unfold torusSource sourceRight
  congr 1
  ext r i
  simp only [torusSourceMatrix, rightMatrix, phase_real]

theorem torusSource_apply (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (t : Torus)
    (u : EuclideanSpace ℂ (Fin N)) (r : Edge20) :
    torusSource edges W t u r = profile edges (Maxwell.Defect.complexSqrtWeightOperator W u) t r := by
  simp only [torusSource, rectangularMap_apply, Matrix.mulVec, dotProduct, torusSourceMatrix,
    profile, Maxwell.Defect.complexSqrtWeightOperator_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- The continuous density is an actual finite resolvent compression. -/
def torusBlock (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (z : ℝ) (t : Torus) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (torusSource edges W t).adjoint.comp
    ((Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (inverseElectricSymbol m z t)).comp
      (torusSource edges W t))

theorem torusBlock_continuous (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (z : ℝ) : Continuous (torusBlock edges W m z) := by
  unfold torusBlock
  apply Continuous.clm_comp
  · exact ContinuousLinearMap.adjoint.continuous.comp (torusSource_continuous edges W)
  · apply Continuous.clm_comp
    · exact ((Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous).comp
        (inverseElectricSymbol m z).continuous
    · exact torusSource_continuous edges W

theorem torusBlock_readout (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (t : Torus) (u : EuclideanSpace ℂ (Fin N)) :
    scalarOperatorReadout u (torusBlock edges W m z t) =
      scalarAmplitude edges (Maxwell.Defect.complexSqrtWeightOperator W u) m z t := by
  unfold scalarOperatorReadout torusBlock
  change inner ℂ u ((torusSource edges W t).adjoint
    (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (inverseElectricSymbol m z t)
      (torusSource edges W t u))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inverseElectricSymbol_apply m z hz]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, (Ring.inverse (torusElectric m t - (z : ℂ) • 1)).mulVec
    (torusSource edges W t u) i * star (torusSource edges W t u i)) = _
  simp only [Matrix.mulVec, dotProduct, torusSource_apply, scalarAmplitude]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Equality of every quadratic readout gives equality of the actual full
block, so its operator norm can use the analytic block-contour bound. -/
theorem weightedBlock_eq_integral (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) (n : Site) :
    weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)) n =
      ∫ t : Torus, UnitAddTorus.mFourier n t • torusBlock edges W m z t := by
  have hint : Integrable (fun t : Torus => UnitAddTorus.mFourier n t • torusBlock edges W m z t) :=
    ((UnitAddTorus.mFourier n).continuous.smul (torusBlock_continuous edges W m z)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro u
  apply star_injective
  simp only [Complex.star_def, inner_conj_symm]
  change scalarOperatorReadout u (weightedBlock edges W _ n) =
    scalarOperatorReadout u (∫ t : Torus, UnitAddTorus.mFourier n t • torusBlock edges W m z t)
  rw [← (scalarOperatorReadout u).integral_comp_comm hint]
  simp only [map_smul, smul_eq_mul, torusBlock_readout edges W m z hz]
  exact weightedBlock_integral edges W u m K hK hm z hz n

/-- The finite matrix inverse is exactly the analytic operator inverse. -/
theorem matrixInverse_operator (A : Matrix Edge20 Edge20 ℂ) :
    Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (Ring.inverse A) =
      (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) A).inverse := by
  have h := ringEquiv_map_ringInverse
    (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).toRingEquiv A
  change Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (Ring.inverse A) =
    Ring.inverse (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) A) at h
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at h
  exact h

theorem torusBlock_angular (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) (q : Fin 3 → ℝ) :
    torusBlock edges W m z (angularTorusPoint q) =
      (sourceLeft edges W (realMomentum q)).comp
        ((Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
          (torusElectric m (angularTorusPoint q) - (z : ℂ) • 1)).inverse.comp
          (sourceRight edges W (realMomentum q))) := by
  unfold torusBlock
  rw [torusSource_angular, ← sourceLeft_real_adjoint, inverseElectricSymbol_apply m z hz,
    matrixInverse_operator]

/-- Angular-coordinate version of the actual full weighted block identity,
with exactly the normalization and phase of the analytic contour proof. -/
theorem weightedBlock_eq_angular_integral (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (v : Site) (d : ℕ) :
    weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1))
      (fun i => (d : ℤ) * v i) =
      (1 / (2 * Real.pi)^3 : ℝ) •
        ∫ q, torusFourierFactor d v q • torusBlock edges W m z (angularTorusPoint q)
          ∂torusCubeMeasure (-Real.pi) (2 * Real.pi) := by
  rw [weightedBlock_eq_integral edges W m K hK hm z hz]
  have hc := (UnitAddTorus.mFourier (fun i => (d : ℤ)*v i)).continuous.smul
    (torusBlock_continuous edges W m z)
  have h := integral_angularTorus
    (fun t => UnitAddTorus.mFourier (fun i => (d : ℤ)*v i) t • torusBlock edges W m z t)
    hc.aestronglyMeasurable
  have hvol : (volume : Measure Torus) = Maxwell.Defect.TorusChart.haar := by
    rfl
  rw [← hvol] at h
  simpa only [mFourier_angularTorusPoint_direction] using h

end
end Maxwell.Green.SourceProfile
