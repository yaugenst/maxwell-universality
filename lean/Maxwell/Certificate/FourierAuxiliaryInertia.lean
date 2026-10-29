import Maxwell.Certificate.FourierElectricInertia

/-! The moving longitudinal correction makes the auxiliary longitudinal
block positive while retaining the exact transverse magnetic spectrum. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open scoped ComplexConjugate

def longitudinalProjectionMatrix (c : Momentum) : Matrix Electric Electric ℂ :=
  fun i j => if i.2 = j.2 then gradientProjectionMatrix c i.2 i.1 j.1 else 0

theorem longitudinalProjection_component (c : Momentum) (f : Frequency) (x : FourierSpace) :
    frequencyComponent f ((longitudinalProjectionMatrix c).toEuclideanLin x) =
      gradientProjection c f (frequencyComponent f x) := by
  rw [← gradientProjectionMatrix_apply]
  apply WithLp.ofLp_injective 2
  funext i
  change (longitudinalProjectionMatrix c *ᵥ x.ofLp) (i, f) =
    (gradientProjectionMatrix c f *ᵥ (fun j => x (j, f))) i
  simp [longitudinalProjectionMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem longitudinalProjection_hermitian (c : Momentum) :
    (longitudinalProjectionMatrix c).IsHermitian := by
  ext i j
  by_cases hf : i.2 = j.2
  · simp [longitudinalProjectionMatrix, Matrix.conjTranspose_apply, hf,
      gradientProjectionMatrix]
    ring
  · simp [longitudinalProjectionMatrix, Matrix.conjTranspose_apply, hf, Ne.symm hf]

theorem longitudinalProjection_symmetric (c : Momentum) :
    (longitudinalProjectionMatrix c).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (longitudinalProjection_hermitian c)

theorem longitudinalProjection_transverse (c : Momentum) (x : FourierSpace)
    (hx : x ∈ transverseSubspace c) :
    (longitudinalProjectionMatrix c).toEuclideanLin x = 0 := by
  apply WithLp.ofLp_injective 2
  funext e
  have h := longitudinalProjection_component c e.2 x
  rw [gradientProjection_apply, show divergenceSymbol c e.2 (frequencyComponent e.2 x) = 0
    from hx e.2, zero_div, zero_smul] at h
  exact congrArg (fun y : Polarization => y e.1) h

theorem longitudinalProjection_mem_orthogonal (c : Momentum) (x : FourierSpace) :
    (longitudinalProjectionMatrix c).toEuclideanLin x ∈ (transverseSubspace c)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [← longitudinalProjection_symmetric c, longitudinalProjection_transverse c y hy,
    inner_zero_left]

theorem sub_longitudinalProjection_mem_transverse (c : Momentum)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) (x : FourierSpace) :
    x - (longitudinalProjectionMatrix c).toEuclideanLin x ∈ transverseSubspace c := by
  intro f
  change divergenceSymbol c f
    (frequencyComponent f (x - (longitudinalProjectionMatrix c).toEuclideanLin x)) = 0
  rw [map_sub, longitudinalProjection_component, map_sub,
    divergence_gradientProjection c f (hlap f), sub_self]

theorem longitudinalProjection_longitudinal (c : Momentum)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) (x : (transverseSubspace c)ᗮ) :
    (longitudinalProjectionMatrix c).toEuclideanLin x = x := by
  have ht := sub_longitudinalProjection_mem_transverse c hlap x
  have ho := (transverseSubspace c)ᗮ.sub_mem x.property (longitudinalProjection_mem_orthogonal c x)
  have hz : (x : FourierSpace) - (longitudinalProjectionMatrix c).toEuclideanLin x = 0 := by
    exact (Submodule.disjoint_def.mp (transverseSubspace c).orthogonal_disjoint) _ ht ho
  exact (sub_eq_zero.mp hz).symm

def auxiliaryMagneticFourier (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t t' : ℝ) : Matrix Electric Electric ℂ :=
  shiftedMagneticFourier material c t' + (2 * t : ℂ) • longitudinalProjectionMatrix c

theorem auxiliaryMagneticFourier_hermitian
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ) :
    (auxiliaryMagneticFourier material c t t').IsHermitian :=
  (shiftedMagneticFourier_hermitian material c t').add
    ((longitudinalProjection_hermitian c).smul
      (by simp : star (2 * (t : ℂ)) = 2 * (t : ℂ)))

theorem auxiliaryMagneticFourier_symmetric
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ) :
    (auxiliaryMagneticFourier material c t t').toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (auxiliaryMagneticFourier_hermitian material c t t')

theorem auxiliaryMagneticFourier_transverse
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) :
    (auxiliaryMagneticFourier material c t t').toEuclideanLin x =
      (shiftedMagneticFourier material c t').toEuclideanLin x := by
  simp only [auxiliaryMagneticFourier, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, longitudinalProjection_transverse c x hx,
    smul_zero, add_zero]

theorem auxiliaryMagneticFourier_invariant
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) :
    (auxiliaryMagneticFourier material c t t').toEuclideanLin x ∈ transverseSubspace c := by
  rw [auxiliaryMagneticFourier_transverse material c t t' x hx]
  exact shiftedMagneticFourier_invariant material c t' x hx

theorem auxiliaryMagneticFourier_restrict
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ) :
    (auxiliaryMagneticFourier material c t t').toEuclideanLin.restrict
      (auxiliaryMagneticFourier_invariant material c t t') =
      transverseMagneticOperator material c t' := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact auxiliaryMagneticFourier_transverse material c t t' x x.property

theorem auxiliaryMagneticFourier_longitudinal
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) (x : (transverseSubspace c)ᗮ) :
    (auxiliaryMagneticFourier material c t t').toEuclideanLin x =
      ((2 * t - t' : ℝ) : ℂ) • (x : FourierSpace) := by
  simp only [auxiliaryMagneticFourier, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, shiftedMagneticFourier_longitudinal material c t' x,
    longitudinalProjection_longitudinal c hlap x, ← add_smul]
  congr 1
  push_cast
  ring

private theorem negative_count_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {A B : H →ₗ[ℂ] H} (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  subst B
  rfl

/-- A positive corrected longitudinal block contributes no negative
eigenvalues. The auxiliary full-space count is exactly transverse inertia. -/
theorem auxiliaryMagneticFourier_negative_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (hpositive : 0 < 2 * t - t') (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material c t t').eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material c t').eigenvalues rfl i < 0).card := by
  have h := negative_count_of_scalar_complement
    (auxiliaryMagneticFourier material c t t').toEuclideanLin
    (auxiliaryMagneticFourier_symmetric material c t t') (transverseSubspace c)
    (auxiliaryMagneticFourier_invariant material c t t') (2 * t - t')
    (auxiliaryMagneticFourier_longitudinal material c t t' hlap)
  rw [ite_eq_right (not_lt.mpr (le_of_lt hpositive)), add_zero] at h
  exact h.trans (negative_count_congr (auxiliaryMagneticFourier_restrict material c t t') _ _)

private theorem zero_count_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {A B : H →ₗ[ℂ] H} (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i = 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i = 0).card := by
  subst B
  rfl

theorem auxiliaryMagneticFourier_zero_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (hpositive : 0 < 2 * t - t') (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material c t t').eigenvalues rfl i = 0).card =
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material c t').eigenvalues rfl i = 0).card := by
  have h := zero_count_of_scalar_complement
    (auxiliaryMagneticFourier material c t t').toEuclideanLin
    (auxiliaryMagneticFourier_symmetric material c t t') (transverseSubspace c)
    (auxiliaryMagneticFourier_invariant material c t t') (2 * t - t')
    (auxiliaryMagneticFourier_longitudinal material c t t' hlap)
  rw [ite_eq_right (ne_of_gt hpositive), add_zero] at h
  exact h.trans (zero_count_congr (auxiliaryMagneticFourier_restrict material c t t') _ _)

theorem magnetic_negative_count_eq_auxiliary_add_longitudinal
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (ht' : 0 < t') (hpositive : 0 < 2 * t - t')
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c t').eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material c t t').eigenvalues rfl i < 0).card + 2000 := by
  rw [shiftedMagneticFourier_negative_count material c t' ht' hlap,
    auxiliaryMagneticFourier_negative_count material c t t' hpositive hlap]

/-- At the physical threshold, an auxiliary full-space certificate gives
the actual primitive electric count after adding the 2000 gradient modes. -/
theorem electric_negative_count_eq_auxiliary_add_longitudinal
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t : ℝ)
    (hm : ∀ e, 0 < edgeAverage material e) (hpositive : 0 < 2 * t - 1 / 64)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (auxiliaryMagneticFourier_symmetric material c t (1 / 64)).eigenvalues rfl i < 0).card + 2000 := by
  rw [electricFiber_transverse_negative_count material c hm hlap,
    auxiliaryMagneticFourier_negative_count material c t (1 / 64) hpositive hlap]

end Maxwell.Certificate.FourierBinding
