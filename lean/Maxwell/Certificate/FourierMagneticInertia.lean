import Maxwell.Certificate.FourierCoercivity
import Maxwell.Spectral.InertiaRestriction

/-! The actual magnetic Fourier operator preserves the transverse subspace.
Its longitudinal complement contributes precisely 2000 negative eigenvalues
at a positive threshold. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)
open scoped ComplexConjugate

theorem divergence_curlSymbolMatrix (c : Momentum) (f : Frequency) (x : Polarization) :
    divergenceSymbol c f ((curlSymbolMatrix c f).toEuclideanLin x) = 0 := by
  simp [divergenceSymbol, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct, curlSymbolMatrix, Fin.sum_univ_three]
  ring

theorem frequencyCurl_mem_transverse (c : Momentum) (x : FourierSpace) :
    (frequencyCurl c).toEuclideanLin x ∈ transverseSubspace c := by
  intro f
  change divergenceSymbol c f (frequencyComponent f ((frequencyCurl c).toEuclideanLin x)) = 0
  rw [frequencyCurl_component]
  exact divergence_curlSymbolMatrix c f (frequencyComponent f x)

theorem inverseMass_hermitian (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) :
    (inverseMass material).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  change star (fun e => ((edgeAverage material e : ℂ))⁻¹) = _
  funext e
  simp

theorem fourierInverseMass_hermitian (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) :
    (fourierInverseMass material).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul (electricTransform 0) (inverseMass_hermitian material)

theorem shiftedMagneticFourier_hermitian (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) : (shiftedMagneticFourier material c t).IsHermitian := by
  apply (Matrix.isHermitian_mul_mul_conjTranspose (frequencyCurl c)
    (fourierInverseMass_hermitian material)).sub
  exact Matrix.isHermitian_one.smul (by simp : star (t : ℂ) = (t : ℂ))

theorem shiftedMagneticFourier_symmetric (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) : (shiftedMagneticFourier material c t).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (shiftedMagneticFourier_hermitian material c t)

theorem shiftedMagneticFourier_invariant (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) (x : FourierSpace) (hx : x ∈ transverseSubspace c) :
    (shiftedMagneticFourier material c t).toEuclideanLin x ∈ transverseSubspace c := by
  simp only [shiftedMagneticFourier, map_sub, map_smul, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.comp_apply]
  exact (transverseSubspace c).sub_mem (frequencyCurl_mem_transverse c _)
    ((transverseSubspace c).smul_mem _ hx)

def transverseMagneticOperator (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) : transverseSubspace c →ₗ[ℂ] transverseSubspace c :=
  (shiftedMagneticFourier material c t).toEuclideanLin.restrict
    (shiftedMagneticFourier_invariant material c t)

theorem transverseMagneticOperator_symmetric (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := ↥(transverseSubspace c))
      (transverseMagneticOperator material c t) :=
  (shiftedMagneticFourier_symmetric material c t).restrict_invariant
    (shiftedMagneticFourier_invariant material c t)

theorem frequencyCurl_adjoint_longitudinal (c : Momentum)
    (x : (transverseSubspace c)ᗮ) :
    (frequencyCurl c).conjTranspose.toEuclideanLin x = 0 := by
  have hr : (frequencyCurl c).toEuclideanLin.range ≤ transverseSubspace c := by
    rintro y ⟨z, rfl⟩
    exact frequencyCurl_mem_transverse c z
  have hx := Submodule.orthogonal_le hr x.property
  rw [LinearMap.orthogonal_range] at hx
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact hx

theorem shiftedMagneticFourier_longitudinal
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t : ℝ)
    (x : (transverseSubspace c)ᗮ) :
    (shiftedMagneticFourier material c t).toEuclideanLin x = (-t : ℂ) • (x : FourierSpace) := by
  simp only [shiftedMagneticFourier, map_sub, map_smul, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_one, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.comp_apply, frequencyCurl_adjoint_longitudinal c x,
    map_zero, zero_sub, neg_smul]

theorem longitudinal_finrank (c : Momentum) (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (transverseSubspace c)ᗮ = 2000 := by
  have hd := (transverseSubspace c).finrank_add_finrank_orthogonal
  rw [transverseSubspace_finrank c hlap] at hd
  have hf : Module.finrank ℂ FourierSpace = 6000 := by
    simp [FourierSpace, Electric, Cell]
  rw [hf] at hd
  omega

/-- The full magnetic negative inertia is the actual transverse negative
inertia plus the 2000 longitudinal modes. -/
theorem shiftedMagneticFourier_negative_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) (t : ℝ)
    (ht : 0 < t) (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c t).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material c t).eigenvalues rfl i < 0).card + 2000 := by
  have h := Maxwell.Spectral.negative_count_of_scalar_complement
    (shiftedMagneticFourier material c t).toEuclideanLin
    (shiftedMagneticFourier_symmetric material c t) (transverseSubspace c)
    (shiftedMagneticFourier_invariant material c t) (-t)
    (fun x => by simpa only [Complex.ofReal_neg] using
      shiftedMagneticFourier_longitudinal material c t x)
  rw [ite_eq_left (neg_lt_zero.mpr ht), longitudinal_finrank c hlap] at h
  exact h


end Maxwell.Certificate.FourierBinding
