import Maxwell.Spectral.Bloch
import Maxwell.Spectral.SpectrumUnion

/-!
# Spectrum of the actual infinite periodic Yee operator

The lattice-to-torus unitary and the matrix multiplication representation are
identified by their proved almost-everywhere actions.  The spectrum equality
therefore applies to the concrete infinite operator, with the same conventional
cell matrix and boundary gauge as the finite certificates.
-/

namespace Maxwell.Spectral.BlochSpectrum

open MeasureTheory Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open scoped ENNReal

noncomputable section


local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The continuous conventional-cell curl symbol on the normalized torus. -/
def curlSymbol : C(Torus, Matrix Edge20 Edge20 ℂ) :=
  ⟨torusCurl, torusCurl_continuous⟩

/-- The constant diagonal symbol of a periodic edge mass. -/
def materialSymbol (m : Edge20 → ℝ) : C(Torus, Matrix Edge20 Edge20 ℂ) :=
  ContinuousMap.const Torus (Matrix.diagonal (fun e => (m e : ℂ)))

private def matrixQuadraticSymbol {X n : Type*}
    [TopologicalSpace X] [Fintype n] (f g : C(X, Matrix n n ℂ)) (a : ℂ) :
    C(X, Matrix n n ℂ) := star f * f - a • g

/-- The full electric symbol, formed in the algebra of continuous matrices. -/
def electricSymbol (m : Edge20 → ℝ) : C(Torus, Matrix Edge20 Edge20 ℂ) :=
  matrixQuadraticSymbol curlSymbol (materialSymbol m) (1 / 64)

@[simp]
theorem electricSymbol_apply (m : Edge20 → ℝ) (t : Torus) :
    electricSymbol m t = torusElectric m t := by
  simp only [electricSymbol, matrixQuadraticSymbol, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, ContinuousMap.smul_apply, curlSymbol, materialSymbol,
    ContinuousMap.coe_mk, ContinuousMap.const_apply, torusElectric]
  rfl

private theorem eq_matrixMultiplier_of_ae {X n : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype n] [DecidableEq n] (μ : Measure X) [IsFiniteMeasure μ]
    (T : MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ)
    (f : C(X, Matrix n n ℂ))
    (h : ∀ u i, T u i =ᵐ[μ] fun t => (f t).mulVec (fun j => u j t) i) :
    T = matrixMultiplier μ f := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact Lp.ext ((h u i).trans (matrixMultiplier_ae μ f u i).symm)

private theorem matrixMultiplier_quadratic {X n : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype n] [DecidableEq n] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : C(X, Matrix n n ℂ)) (a : ℂ) :
    (matrixMultiplier μ f).adjoint.comp (matrixMultiplier μ f) -
      a • matrixMultiplier μ g = matrixMultiplier μ (matrixQuadraticSymbol f g a) := by
  change star (matrixMultiplierHom μ f) * matrixMultiplierHom μ f -
    a • matrixMultiplierHom μ g = matrixMultiplierHom μ (star f * f - a • g)
  simp only [map_sub, map_mul, map_smul, map_star]

private theorem factorization_eq_matrixMultiplier {X n : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype n] [DecidableEq n] (μ : Measure X) [IsFiniteMeasure μ]
    (H T U : MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ)
    (f g : C(X, Matrix n n ℂ)) (a : ℂ)
    (hH : H = T.adjoint.comp T - a • U)
    (hT : T = matrixMultiplier μ f) (hU : U = matrixMultiplier μ g) :
    H = matrixMultiplier μ (matrixQuadraticSymbol f g a) := by
  rw [hH, hT, hU]
  exact matrixMultiplier_quadratic μ f g a

theorem fiberCurl_eq_matrixMultiplier :
    fiberCurl = matrixMultiplier volume curlSymbol := by
  apply eq_matrixMultiplier_of_ae
  intro u e
  exact fiberCurl_ae u e

theorem fiberMaterial_eq_matrixMultiplier (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    fiberMaterial m K hK hm = matrixMultiplier volume (materialSymbol m) := by
  apply eq_matrixMultiplier_of_ae
  intro u e
  filter_upwards [fiberMaterial_ae m K hK hm u e] with t h
  rw [h]
  simp [materialSymbol, Matrix.mulVec_diagonal]

/-- Exact unitary equivalence between the infinite Yee operator and actual
multiplication by the finite electric matrix. -/
theorem transform_electric_eq_matrixMultiplier (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    transform.conjStarAlgEquiv (electricOperator (periodicCoefficient m) K hK hm) =
      matrixMultiplier volume (electricSymbol m) := by
  exact factorization_eq_matrixMultiplier volume
    (transform.conjStarAlgEquiv (electricOperator (periodicCoefficient m) K hK hm))
    fiberCurl (fiberMaterial m K hK hm) curlSymbol (materialSymbol m) (1 / 64)
    (transform_electricOperator m K hK hm) fiberCurl_eq_matrixMultiplier
    (fiberMaterial_eq_matrixMultiplier m K hK hm)


/-- No exceptional momenta are removed: normalized Haar measure has full
support and the finite electric symbol is continuous. -/
theorem electricOperator_spectrum_torus (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K) :
    spectrum ℝ (electricOperator (periodicCoefficient m) K hK hm) =
      ⋃ t : Torus, spectrum ℝ (torusElectric m t) := by
  rw [← AlgEquiv.spectrum_eq
    (transform.conjStarAlgEquiv.toAlgEquiv.restrictScalars ℝ)]
  change spectrum ℝ (transform.conjStarAlgEquiv
    (electricOperator (periodicCoefficient m) K hK hm)) = _
  rw [transform_electric_eq_matrixMultiplier]
  exact matrixMultiplier_spectrum_real volume (electricSymbol m)
    (fun t => torusElectric_hermitian m t)

/-- The spectrum of the actual infinite, periodically weighted Yee operator
is the union of the exact conventional-cell Bloch fiber spectra. -/
theorem electricOperator_spectrum_periodic (material : PeriodicYee.Cell20 → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K) :
    spectrum ℝ (electricOperator
      (periodicCoefficient (PeriodicYee.edgeAverage material)) K hK hm) =
      ⋃ k : PeriodicYee.Momentum, spectrum ℝ (PeriodicYee.fiber material k) := by
  rw [electricOperator_spectrum_torus]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨k, rfl⟩ := momentumTorus_surjective t
    exact ⟨k, by simpa only [torusElectric_eq_periodic] using ht⟩
  · rintro ⟨k, hk⟩
    exact ⟨momentumTorus k, by simpa only [torusElectric_eq_periodic] using hk⟩

end

end Maxwell.Spectral.BlochSpectrum
