import Maxwell.Certificate.FourierMagneticInertia
import Maxwell.Spectral.ElectricMagneticInertia
import Maxwell.Spectral.SectorSimplicity

/-! Exact transfer from transverse Fourier magnetic inertia to the actual
primitive electric matrix. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open scoped ComplexOrder

private theorem negative_count_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {A B : H →ₗ[ℂ] H} (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  subst B
  rfl

theorem matrix_negative_count_positive_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.toEuclideanLin.IsSymmetric) (hB : B.toEuclideanLin.IsSymmetric)
    (t : ℝ) (ht : 0 < t) (hscale : B = t • A) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  have hlin : B.toEuclideanLin = t • A.toEuclideanLin := by
    rw [hscale, toEuclideanLin_real_smul]
  have hTA : (t • A.toEuclideanLin).IsSymmetric := hlin ▸ hB
  exact (positive_scalar_negative_count A.toEuclideanLin hA t ht hTA).trans
    (negative_count_congr hlin hB hTA).symm

theorem matrix_negative_count_unitary {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (B : Matrix ι ι ℂ) (U : Matrix κ ι ℂ)
    (hleft : U.conjTranspose * U = 1) (hright : U * U.conjTranspose = 1)
    (hbind : U.conjTranspose * A * U = B)
    (hA : A.toEuclideanLin.IsSymmetric) (hB : B.toEuclideanLin.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  let e := (SectorSimplicity.matrixUnitaryEquiv U hleft hright).toLinearEquiv
  have hform (x : EuclideanSpace ℂ ι) :
      (inner ℂ (e x) (A.toEuclideanLin (e x))).re =
        (inner ℂ x (B.toEuclideanLin x)).re := by
    change (inner ℂ (U.toEuclideanLin x) (A.toEuclideanLin (U.toEuclideanLin x))).re = _
    rw [← hbind]
    simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact congrArg Complex.re (LinearMap.adjoint_inner_right U.toEuclideanLin _ _).symm
  exact (eigenvalue_inertia_congruence hB hA e hform).1.symm

theorem inverseMass_eq_mass_inv (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 0 < edgeAverage material e) :
    inverseMass material = (mass material)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [inverseMass, mass, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))]
  · simp [hij]

theorem magneticFiber_hermitian (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (k : Momentum) : (magneticFiber material k).IsHermitian := by
  apply (Matrix.isHermitian_mul_mul_conjTranspose (curl k) (inverseMass_hermitian material)).sub
  exact Matrix.isHermitian_one.smul (by simp : star (1 / 64 : ℂ) = (1 / 64 : ℂ))

theorem magneticFiber_symmetric (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (k : Momentum) : (magneticFiber material k).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (magneticFiber_hermitian material k)

/-- The physical boundary-gauge magnetic fiber and the fixed Fourier
magnetic matrix have exactly the same negative inertia. -/
theorem magneticFiber_fourier_negative_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum) :
    (Finset.univ.filter fun i =>
      (magneticFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c (1 / 64)).eigenvalues rfl i < 0).card :=
  matrix_negative_count_unitary (magneticFiber material (boundaryMomentum c))
    (shiftedMagneticFourier material c (1 / 64)) (electricTransform c)
    (electricTransform_conjTranspose_mul c) (electricTransform_mul_conjTranspose c)
    (by simpa only [shiftedMagneticFourier, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using magneticFiber_fixed_fourier material c) _ _

theorem electricFiber_symmetric (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (k : Momentum) : (fiber material k).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (fiber_hermitian material k)

/-- Positivity of actual edge averages suffices for the electric/magnetic
Schur inertia identity at the fixed physical threshold `1/64`. -/
theorem electric_magnetic_physical_negative_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (k : Momentum)
    (hm : ∀ e, 0 < edgeAverage material e) :
    (Finset.univ.filter fun i => (electricFiber_symmetric material k).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i => (magneticFiber_symmetric material k).eigenvalues rfl i < 0).card := by
  have hmass : (mass material).PosDef :=
    Matrix.PosDef.diagonal fun e => Complex.zero_lt_real.mpr (hm e)
  let M : Matrix Electric Electric ℂ := (1 / 64 : ℝ) • mass material
  have hM : M.PosDef := hmass.smul (by norm_num : (0 : ℝ) < 1 / 64)
  let B : Matrix Electric Electric ℂ := curl k * M⁻¹ * (curl k).conjTranspose - 1
  have hB : B.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.isHermitian_mul_mul_conjTranspose (curl k) hM.isHermitian.inv).sub
      Matrix.isHermitian_one)
  have heq : (curl k).conjTranspose * curl k - M = fiber material k := by
    change (curl k).conjTranspose * curl k - (1 / 64 : ℝ) • mass material = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num [fiber]
  have hE : ((curl k).conjTranspose * curl k - M).toEuclideanLin.IsSymmetric :=
    heq.symm ▸ electricFiber_symmetric material k
  have hc := electric_magnetic_negative_count_eq (curl k) M hM rfl hE hB
  have hscale : magneticFiber material k = (1 / 64 : ℝ) • B := by
    rw [magneticFiber, inverseMass_eq_mass_inv material hm]
    have h := scaled_magnetic_identity_real (curl k) (mass material) hmass.isUnit
      (1 / 64) (by norm_num)
    change (1 / 64 : ℝ) • B = _ at h
    rw [h]
    congr 1
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num
  have hs := matrix_negative_count_positive_scale B (magneticFiber material k)
    hB (magneticFiber_symmetric material k) (1 / 64) (by norm_num) hscale
  have hElin := congrArg (fun A : Matrix Electric Electric ℂ => A.toEuclideanLin) heq
  exact (negative_count_congr hElin hE (electricFiber_symmetric material k)).symm.trans
    (hc.trans hs)

/-- Direct electric-to-transverse count identity for the actual primitive
Yee matrices at Cartesian Fourier momentum. -/
theorem electricFiber_transverse_negative_count
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (c : Momentum)
    (hm : ∀ e, 0 < edgeAverage material e) (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (transverseMagneticOperator_symmetric material c (1 / 64)).eigenvalues rfl i < 0).card + 2000 :=
  (electric_magnetic_physical_negative_count material (boundaryMomentum c) hm).trans
    ((magneticFiber_fourier_negative_count material c).trans
      (shiftedMagneticFourier_negative_count material c (1 / 64) (by norm_num) hlap))

theorem primitive_edgeAverage_uniform_shift
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (a : ℝ) (e : Electric) :
    edgeAverage (fun r => material r + a) e = edgeAverage material e + a := by
  rw [edgeAverage_binding, edgeAverage_binding]
  exact Maxwell.Spectral.PeriodicYee.edgeAverage_shift material a _

/-- The endpoint material shift is exactly the scalar electric energy
shift in primitive coordinates. -/
theorem primitive_fiber_uniform_shift
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ) (s : ℝ) (k : Momentum) :
    fiber (fun r => material r + 64 * s) k = fiber material k - (s : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [fiber, mass, primitive_edgeAverage_uniform_shift]
    ring
  · simp [fiber, mass, hij]

end Maxwell.Certificate.FourierBinding
