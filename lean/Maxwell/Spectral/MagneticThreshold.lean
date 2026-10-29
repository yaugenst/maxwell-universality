import Maxwell.Certificate.FourierElectricInertia
import Maxwell.Spectral.ConcretePerturbation

/-! Electric/magnetic inertia at an arbitrary positive frequency, and
Loewner conversion of the resulting counts to actual electric energy thresholds. -/

noncomputable section
namespace Maxwell.Spectral.MagneticThreshold
open Matrix Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open scoped ComplexOrder

def electric (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    Matrix Electric Electric ℂ := (curl k).conjTranspose * curl k - (t : ℂ) • mass material

def magnetic (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    Matrix Electric Electric ℂ := curl k * inverseMass material * (curl k).conjTranspose - (t : ℂ) • 1

theorem electric_hermitian (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    (electric material k t).IsHermitian :=
  (Matrix.isHermitian_conjTranspose_mul_self (curl k)).sub
    ((mass_hermitian material).smul (by simp : star (t : ℂ) = (t : ℂ)))

theorem magnetic_hermitian (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    (magnetic material k t).IsHermitian :=
  (Matrix.isHermitian_mul_mul_conjTranspose (curl k) (inverseMass_hermitian material)).sub
    (Matrix.isHermitian_one.smul (by simp : star (t : ℂ) = (t : ℂ)))

theorem electric_symmetric (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    (electric material k t).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (electric_hermitian material k t)

theorem magnetic_symmetric (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ) :
    (magnetic material k t).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (magnetic_hermitian material k t)

theorem magnetic_fourier (material : PeriodicYee.Cell20 → ℝ) (c : Momentum) (t : ℝ) :
    (electricTransform c).conjTranspose * magnetic material (boundaryMomentum c) t *
      electricTransform c = shiftedMagneticFourier material c t := by
  unfold magnetic shiftedMagneticFourier fourierInverseMass
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, electricTransform_conjTranspose_mul]
  rw [unitary_compression_mul _ _ _ (electricTransform_mul_conjTranspose c),
    unitary_compression_mul _ _ _ (electricTransform_mul_conjTranspose c),
    curl_diagonalized, curl_adjoint_diagonalized]
  rw [inverseMass, diagonal_compression_eq_zero]

private theorem negative_count_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {A B : H →ₗ[ℂ] H} (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  subst B
  rfl

/-- Actual primitive electric and full magnetic negative counts agree at
any positive threshold. No nonzero Fourier-symbol premise is needed. -/
theorem electric_threshold_negative_count (material : PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (t : ℝ) (ht : 0 < t) (hm : ∀ e, 0 < edgeAverage material e) :
    (Finset.univ.filter fun i =>
      (electric_symmetric material (boundaryMomentum c) t).eigenvalues rfl i < 0).card =
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c t).eigenvalues rfl i < 0).card := by
  let k := boundaryMomentum c
  have hmass : (mass material).PosDef :=
    Matrix.PosDef.diagonal fun e => Complex.zero_lt_real.mpr (hm e)
  let M : Matrix Electric Electric ℂ := t • mass material
  have hM : M.PosDef := hmass.smul ht
  let B : Matrix Electric Electric ℂ := curl k * M⁻¹ * (curl k).conjTranspose - 1
  have hB : B.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.isHermitian_mul_mul_conjTranspose (curl k) hM.isHermitian.inv).sub
      Matrix.isHermitian_one)
  have heq : (curl k).conjTranspose * curl k - M = electric material k t := by
    simp only [M, electric, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hE : ((curl k).conjTranspose * curl k - M).toEuclideanLin.IsSymmetric :=
    heq.symm ▸ electric_symmetric material k t
  have hc := electric_magnetic_negative_count_eq (curl k) M hM rfl hE hB
  have hscale : magnetic material k t = t • B := by
    rw [magnetic, inverseMass_eq_mass_inv material hm]
    have h := scaled_magnetic_identity_real (curl k) (mass material) hmass.isUnit t ht.ne'
    change t • B = _ at h
    rw [h, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hs := matrix_negative_count_positive_scale B (magnetic material k t)
    hB (magnetic_symmetric material k t) t ht hscale
  have hElin := congrArg (fun A : Matrix Electric Electric ℂ => A.toEuclideanLin) heq
  have he := (negative_count_congr hElin hE (electric_symmetric material k t)).symm.trans
    (hc.trans hs)
  exact he.trans (matrix_negative_count_unitary (magnetic material k t)
    (shiftedMagneticFourier material c t) (electricTransform c)
    (electricTransform_conjTranspose_mul c) (electricTransform_mul_conjTranspose c)
    (magnetic_fourier material c t) _ _)

/-- Ordered quadratic comparison transfers a negative count monotonically. -/
theorem negative_count_mono {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A B : H →ₗ[ℂ] H) (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : ∀ x, (inner ℂ x (A x)).re ≤ (inner ℂ x (B x)).re) :
    (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card ≤
      (Finset.univ.filter fun i => hA.eigenvalues rfl i < 0).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact (eigenvalues_mono_of_quadratic_le hA hB hAB i).trans_lt hi

theorem mass_form_lower (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (x : FourierSpace) :
    ‖x‖^2 ≤ (inner ℂ x ((mass material).toEuclideanLin x)).re := by
  have hquad : (inner ℂ x ((mass material).toEuclideanLin x)).re =
      ∑ e, edgeAverage material e * ‖x e‖^2 := by
    have h := diagonal_quadratic_form (EuclideanSpace.basisFun Electric ℂ)
      (fun e => edgeAverage material e) (T := (mass material).toEuclideanLin) ?_ x
    · simpa only [EuclideanSpace.basisFun_repr] using h
    · intro y e
      simp [mass, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec_diagonal, EuclideanSpace.basisFun_repr]
  rw [hquad, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum fun e _ => by nlinarith [hm e, sq_nonneg ‖x e‖]

def energyShift (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (s : ℝ) :
    Matrix Electric Electric ℂ := fiber material k - (s : ℂ) • 1

theorem energyShift_symmetric (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (s : ℝ) :
    (energyShift material k s).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr ((fiber_hermitian material k).sub
    (Matrix.isHermitian_one.smul (by simp : star (s : ℂ) = (s : ℂ))))

theorem energy_threshold_count (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (s : ℝ) :
    (Finset.univ.filter fun i => (electricFiber_symmetric material k).eigenvalues rfl i < s).card =
    (Finset.univ.filter fun i => (energyShift_symmetric material k s).eigenvalues rfl i < 0).card := by
  apply threshold_count_eq_negative_of_shift
  simp only [energyShift, map_sub, map_smul, Matrix.toLpLin_one]

theorem electric_form (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (t : ℝ)
    (x : FourierSpace) :
    (inner ℂ x ((electric material k t).toEuclideanLin x)).re =
      (inner ℂ x (((curl k).conjTranspose*curl k).toEuclideanLin x)).re -
      t*(inner ℂ x ((mass material).toEuclideanLin x)).re := by
  simp only [electric, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_sub_right, Complex.sub_re, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem energyShift_form (material : PeriodicYee.Cell20 → ℝ) (k : Momentum) (s : ℝ)
    (x : FourierSpace) :
    (inner ℂ x ((energyShift material k s).toEuclideanLin x)).re =
      (inner ℂ x (((curl k).conjTranspose*curl k).toEuclideanLin x)).re -
      (1/64)*(inner ℂ x ((mass material).toEuclideanLin x)).re - s*‖x‖^2 := by
  have h : fiber material k = electric material k (1/64) := by
    simp only [fiber, electric, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp only [energyShift, h, map_sub, map_smul, Matrix.toLpLin_one, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, Complex.sub_re,
    inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, electric_form]

/-- A magnetic upper count at `t+s` bounds the number of actual electric
eigenvalues below energy `s`, using only the physical lower mass bound. -/
theorem energy_threshold_upper (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum) (s : ℝ) (hs : 0 ≤ s) :
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < s).card ≤
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c (1/64+s)).eigenvalues rfl i < 0).card := by
  rw [energy_threshold_count, ← electric_threshold_negative_count material c _
    (by linarith) (fun e => by linarith [hm e])]
  apply negative_count_mono
  intro x
  rw [electric_form, energyShift_form]
  have h := mul_nonneg hs (sub_nonneg.mpr (mass_form_lower material hm x))
  nlinarith

/-- A magnetic lower count at `t-s` certifies that many actual electric
eigenvalues below `-s`; it does not require a high-frequency certificate. -/
theorem energy_threshold_lower (material : PeriodicYee.Cell20 → ℝ)
    (hm : ∀ e, 1 ≤ edgeAverage material e) (c : Momentum) (s : ℝ)
    (hs : 0 ≤ s) (hst : s < 1/64) :
    (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material c (1/64-s)).eigenvalues rfl i < 0).card ≤
    (Finset.univ.filter fun i =>
      (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < -s).card := by
  rw [energy_threshold_count, ← electric_threshold_negative_count material c _
    (by linarith) (fun e => by linarith [hm e])]
  apply negative_count_mono
  intro x
  rw [electric_form, energyShift_form]
  have h := mul_nonneg hs (sub_nonneg.mpr (mass_form_lower material hm x))
  nlinarith

end Maxwell.Spectral.MagneticThreshold
