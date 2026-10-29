import Maxwell.Spectral.BlochSpectrum
import Maxwell.Spectral.MultiplierIntegral
import Maxwell.Spectral.BlochDelta

/-!
# Actual periodic resolvents and their compressed integral formula

The inverse is taken in the algebra of bounded operators.  Its Bloch image is
proved to be multiplication by the inverse finite matrix; the scalar integral
identity then follows from the Hilbert inner product, with normalized Haar
measure on the torus.
-/

namespace Maxwell.Spectral.BlochResolvent

open MeasureTheory Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.BlochSpectrum
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

theorem map_ringInverse_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) {a : A} (ha : IsUnit a) :
    φ (Ring.inverse a) = Ring.inverse (φ a) := by
  rcases ha with ⟨u, rfl⟩
  rw [Ring.inverse_unit]
  change φ (↑u⁻¹) = Ring.inverse (↑(Units.map φ.toMonoidHom u))
  rw [Ring.inverse_unit]
  rfl

theorem ringEquiv_map_ringInverse {A B : Type*} [Ring A] [Ring B]
    (φ : A ≃+* B) (a : A) : φ (Ring.inverse a) = Ring.inverse (φ a) := by
  by_cases h : IsUnit a
  · exact map_ringInverse_of_isUnit φ.toRingHom h
  · have h' : ¬ IsUnit (φ a) := by
      intro hi
      apply h
      have hp := hi.map φ.symm.toMonoidHom
      change IsUnit (φ.symm (φ a)) at hp
      simpa only [RingEquiv.symm_apply_apply] using hp
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

private def continuousEvalRingHom {X R : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Ring R] [IsTopologicalRing R] (x : X) : C(X, R) →+* R where
  toFun f := f x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_inverse_apply {X R : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    (f : C(X, R)) (hf : IsUnit f) (t : X) :
    Ring.inverse f t = Ring.inverse (f t) :=
  map_ringInverse_of_isUnit (continuousEvalRingHom t) hf

/-- Algebraic transport of a genuine inverse through a unitary algebra
isomorphism and the faithful multiplication representation. -/
theorem transport_shifted_inverse {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (φ : A ≃ₐ[ℂ] B) (ψ : C →ₐ[ℂ] B) (H : A) (f : C) (z : ℂ)
    (hH : φ H = ψ f) (hf : IsUnit (f - z • 1)) :
    φ (Ring.inverse (H - z • 1)) = ψ (Ring.inverse (f - z • 1)) := by
  change φ.toRingEquiv (Ring.inverse (H - z • 1)) = _
  rw [ringEquiv_map_ringInverse]
  change Ring.inverse (φ (H - z • 1)) = _
  rw [map_sub, map_smul, map_one, hH]
  have hs : ψ (f - z • 1) = ψ f - z • 1 := by simp only [map_sub, map_smul, map_one]
  rw [← hs]
  exact (map_ringInverse_of_isUnit ψ.toRingHom hf).symm

theorem continuous_shift_isUnit_of_real_spectrum {X n : Type*}
    [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (f : C(X, Matrix n n ℂ)) (z : ℝ)
    (hz : ∀ t, z ∉ spectrum ℝ (f t)) : IsUnit (f - (z : ℂ) • 1) := by
  apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
  intro t
  have h := (spectrum.notMem_iff.mp (hz t)).neg
  have hs : z • (1 : Matrix n n ℂ) = (z : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    exact Complex.real_smul
  simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, neg_sub, Algebra.algebraMap_eq_smul_one, hs] using h

theorem inner_integral_of_conjugation {X n E : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype n] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (U : E ≃ₗᵢ[ℂ] MatrixL2 (n := n) μ) (T : E →L[ℂ] E)
    (f : C(X, Matrix n n ℂ)) (h : U.conjStarAlgEquiv T = matrixMultiplier μ f)
    (u v : E) :
    inner ℂ u (T v) =
      ∫ t, ∑ i, star (U u i t) * (f t).mulVec (fun j => U v j t) i ∂μ := by
  have ha := congrArg (fun S => S (U v)) h
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at ha
  rw [← U.inner_map_map u (T v), ha]
  exact matrixMultiplier_inner_integral μ f (U u) (U v)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Continuous inverse matrix symbol, with the paper's `(H-z)⁻¹` sign. -/
def inverseElectricSymbol (m : Edge20 → ℝ) (z : ℝ) : C(Torus, Matrix Edge20 Edge20 ℂ) :=
  Ring.inverse (electricSymbol m - (z : ℂ) • 1)

theorem electricSymbol_shift_isUnit (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) :
    IsUnit (electricSymbol m - (z : ℂ) • 1) := by
  exact continuous_shift_isUnit_of_real_spectrum (electricSymbol m) z hz


@[simp]
theorem inverseElectricSymbol_apply (m : Edge20 → ℝ) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) (t : Torus) :
    inverseElectricSymbol m z t = Ring.inverse (torusElectric m t - (z : ℂ) • 1) := by
  rw [inverseElectricSymbol, continuous_inverse_apply _ (electricSymbol_shift_isUnit m z hz)]
  rfl

theorem transform_electric_inverse (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (z : ℝ) (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) :
    transform.conjStarAlgEquiv
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)) =
    matrixMultiplier volume (inverseElectricSymbol m z) := by
  exact transport_shifted_inverse transform.conjStarAlgEquiv.toAlgEquiv
    (matrixMultiplierHom volume).toAlgHom
    (electricOperator (periodicCoefficient m) K hK hm) (electricSymbol m) (z : ℂ)
    (transform_electric_eq_matrixMultiplier m K hK hm) (electricSymbol_shift_isUnit m z hz)

/-- Matrix elements of the actual infinite inverse are normalized torus
integrals of the exact finite inverse matrix. -/
theorem electric_inverse_inner_integral (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (z : ℝ) (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (u v : Field) :
    inner ℂ u (Ring.inverse
      (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1) v) =
    ∫ t : Torus, ∑ i, star (transform u i t) *
      (Ring.inverse (torusElectric m t - (z : ℂ) • 1)).mulVec
        (fun j => transform v j t) i := by
  have h := inner_integral_of_conjugation volume transform
    (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1))
    (inverseElectricSymbol m z) (transform_electric_inverse m K hK hm z hz) u v
  simpa only [inverseElectricSymbol_apply m z hz] using h

private theorem single_bilinear {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (e f : n) (a b : ℂ) :
    (∑ i, star (if i = e then a else 0) *
      A.mulVec (fun j => if j = f then b else 0) i) = star a * A e f * b := by
  simp [Matrix.mulVec, dotProduct, ite_mul, apply_ite, mul_assoc]

/-- The exact finite-support compression entry, including both lattice
translate phases and arbitrary complex source weights. -/
theorem electric_inverse_delta_integral (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (z : ℝ) (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t))
    (e f : Edge) (a b : ℂ) :
    inner ℂ (lp.single 2 e a) (Ring.inverse
      (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)
      (lp.single 2 f b)) =
    ∫ t : Torus,
      star (a * UnitAddTorus.mFourier (-(edgeCellEquiv e).2) t) *
      Ring.inverse (torusElectric m t - (z : ℂ) • 1)
        (edgeCellEquiv e).1 (edgeCellEquiv f).1 *
      (b * UnitAddTorus.mFourier (-(edgeCellEquiv f).2) t) := by
  rw [electric_inverse_inner_integral m K hK hm z hz]
  apply integral_congr_ae
  filter_upwards [Filter.eventually_all.mpr (fun i => transform_single_component_ae e a i),
    Filter.eventually_all.mpr (fun i => transform_single_component_ae f b i)] with t he hf
  simp only [he, hf]
  exact single_bilinear _ _ _ _ _

/-- Resolvent-domain version of the compression formula, with the exclusion
stated for the actual infinite operator itself. -/
theorem electric_inverse_delta_integral_of_notMem (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (z : ℝ)
    (hz : z ∉ spectrum ℝ (electricOperator (periodicCoefficient m) K hK hm))
    (e f : Edge) (a b : ℂ) :
    inner ℂ (lp.single 2 e a) (Ring.inverse
      (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)
      (lp.single 2 f b)) =
    ∫ t : Torus,
      star (a * UnitAddTorus.mFourier (-(edgeCellEquiv e).2) t) *
      Ring.inverse (torusElectric m t - (z : ℂ) • 1)
        (edgeCellEquiv e).1 (edgeCellEquiv f).1 *
      (b * UnitAddTorus.mFourier (-(edgeCellEquiv f).2) t) := by
  apply electric_inverse_delta_integral m K hK hm z
  intro t ht
  apply hz
  rw [electricOperator_spectrum_torus]
  exact Set.mem_iUnion.mpr ⟨t, ht⟩

end

end Maxwell.Spectral.BlochResolvent
