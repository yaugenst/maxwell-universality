import Maxwell.Spectral.InertiaCongruence
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Electric and magnetic inertia from two exact Schur completions of the
same finite block quadratic form. -/

noncomputable section

open Matrix WithLp
open scoped ComplexConjugate ComplexOrder

namespace Maxwell.Spectral

section Shears

variable {H K : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]

def upperShear (f : K →ₗ[ℂ] H) : (H × K) ≃ₗ[ℂ] (H × K) where
  toFun x := (x.1 + f x.2, x.2)
  invFun x := (x.1 - f x.2, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp; abel
  map_smul' c x := by ext <;> simp [smul_add]

def lowerShear (f : H →ₗ[ℂ] K) : (H × K) ≃ₗ[ℂ] (H × K) where
  toFun x := (x.1, x.2 + f x.1)
  invFun x := (x.1, x.2 - f x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp; abel
  map_smul' c x := by ext <;> simp [smul_add]

end Shears

theorem inner_l2ProductMap
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : H →ₗ[ℂ] H) (B : K →ₗ[ℂ] K) (x : WithLp 2 (H × K)) :
    inner ℂ x (l2ProductMap A B x) =
      inner ℂ x.ofLp.1 (A x.ofLp.1) + inner ℂ x.ofLp.2 (B x.ofLp.2) := rfl

section Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def matrixQuadratic (A : Matrix m m ℂ) (x : m → ℂ) : ℂ := star x ⬝ᵥ (A *ᵥ x)

theorem inner_toEuclideanLin (A : Matrix m m ℂ) (x : EuclideanSpace ℂ m) :
    inner ℂ x (A.toEuclideanLin x) = matrixQuadratic A x.ofLp := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, matrixQuadratic, dotProduct_comm]

/-- Completing the same block form in its two diagonal blocks gives the
electric and magnetic complementary quadratic forms exactly. -/
theorem electric_magnetic_schur_form
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) [Invertible M] (hM : M.IsHermitian)
    (x : m → ℂ) (u : n → ℂ) :
    matrixQuadratic M (x + (M⁻¹ * Cᴴ) *ᵥ (u - C *ᵥ x)) +
      matrixQuadratic (1 - C * M⁻¹ * Cᴴ) (u - C *ᵥ x) =
    matrixQuadratic (M - Cᴴ * C) x + matrixQuadratic 1 u := by
  let : Invertible (1 : Matrix n n ℂ) := invertibleOne
  have h₁ := Matrix.schur_complement_eq₁₁ Cᴴ (1 : Matrix n n ℂ) x (u - C *ᵥ x) hM
  have h₂ := Matrix.schur_complement_eq₂₂ M Cᴴ x (u - C *ᵥ x)
    (Matrix.isHermitian_one : (1 : Matrix n n ℂ).IsHermitian)
  have h := h₁.symm.trans h₂
  have hy : C *ᵥ x + (u - C *ᵥ x) = u := by abel
  simpa only [conjTranspose_conjTranspose, inv_one, Matrix.one_mul, Matrix.mul_one,
    hy, matrixQuadratic, dotProduct_mulVec, add_comm] using h

/-- The two Schur coordinate changes are triangular bijections; their
invertibility is independent of whether either Schur complement is singular. -/
def electricMagneticSchurEquiv (C : Matrix n m ℂ) (M : Matrix m m ℂ) :
    WithLp 2 (EuclideanSpace ℂ m × EuclideanSpace ℂ n) ≃ₗ[ℂ]
      WithLp 2 (EuclideanSpace ℂ m × EuclideanSpace ℂ n) :=
  (WithLp.linearEquiv 2 ℂ _).trans
    (((lowerShear (-C.toEuclideanLin)).trans
      (upperShear (M⁻¹ * Cᴴ).toEuclideanLin)).trans (WithLp.linearEquiv 2 ℂ _).symm)

@[simp] theorem electricMagneticSchurEquiv_ofLp
    (C : Matrix n m ℂ) (M : Matrix m m ℂ)
    (x : WithLp 2 (EuclideanSpace ℂ m × EuclideanSpace ℂ n)) :
    (electricMagneticSchurEquiv C M x).ofLp =
      (x.ofLp.1 + (M⁻¹ * Cᴴ).toEuclideanLin (x.ofLp.2 - C.toEuclideanLin x.ofLp.1),
        x.ofLp.2 - C.toEuclideanLin x.ofLp.1) := rfl

theorem electricMagneticSchurEquiv_form
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) [Invertible M] (hM : M.IsHermitian)
    (x : WithLp 2 (EuclideanSpace ℂ m × EuclideanSpace ℂ n)) :
    inner ℂ (electricMagneticSchurEquiv C M x)
        (l2ProductMap M.toEuclideanLin (1 - C * M⁻¹ * Cᴴ).toEuclideanLin
          (electricMagneticSchurEquiv C M x)) =
      inner ℂ x (l2ProductMap (M - Cᴴ * C).toEuclideanLin
        (1 : Matrix n n ℂ).toEuclideanLin x) := by
  rw [inner_l2ProductMap, inner_l2ProductMap]
  rw [electricMagneticSchurEquiv_ofLp]
  simp only [inner_toEuclideanLin, WithLp.ofLp_add, WithLp.ofLp_sub,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  exact electric_magnetic_schur_form C M hM x.ofLp.1.ofLp x.ofLp.2.ofLp

theorem positive_matrix_eigenvalues (M : Matrix m m ℂ) (hM : M.PosDef)
    (hMs : M.toEuclideanLin.IsSymmetric)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ m))) :
    0 < hMs.eigenvalues rfl i := by
  let b := hMs.eigenvectorBasis rfl
  have hx : (b i).ofLp ≠ 0 := by
    intro hx
    exact b.toBasis.ne_zero i (WithLp.ofLp_injective 2 hx)
  have hp := hM.re_dotProduct_pos hx
  change 0 < (matrixQuadratic M (b i).ofLp).re at hp
  rw [← inner_toEuclideanLin] at hp
  have he := hMs.apply_eigenvectorBasis rfl i
  change M.toEuclideanLin (b i) = (hMs.eigenvalues rfl i : ℂ) • b i at he
  rw [he, inner_smul_right] at hp
  simpa only [b, OrthonormalBasis.inner_eq_ite, ite_true, mul_one, Complex.ofReal_re] using hp

theorem negative_matrix_spectral_quadratic_form
    (A : Matrix m m ℂ) (hA : A.toEuclideanLin.IsSymmetric) (x : EuclideanSpace ℂ m) :
    (inner ℂ x ((-A).toEuclideanLin x)).re =
      ∑ i, (-hA.eigenvalues rfl i) * ‖(hA.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
  simp only [map_neg, LinearMap.neg_apply, inner_neg_right, Complex.neg_re,
    spectral_quadratic_form hA, neg_mul, Finset.sum_neg_distrib]

/-- For rectangular curls, the negative multiplicities differ exactly by
the dimensions of the two ambient spaces. No invertibility is required of
the electric or magnetic operator itself. -/
theorem electric_magnetic_negative_count
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) (hM : M.PosDef)
    (hE : (Cᴴ * C - M).toEuclideanLin.IsSymmetric)
    (hB : (C * M⁻¹ * Cᴴ - 1).toEuclideanLin.IsSymmetric) :
    (Finset.univ.filter fun i => hE.eigenvalues rfl i < 0).card + Fintype.card n =
      Fintype.card m + (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  let : Invertible M := hM.isUnit.invertible
  have hMs : M.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM.1
  have he : (M - Cᴴ * C).toEuclideanLin = -(Cᴴ * C - M).toEuclideanLin := by
    rw [show M - Cᴴ * C = -(Cᴴ * C - M) by abel]
    exact map_neg _ _
  have hb : (1 - C * M⁻¹ * Cᴴ).toEuclideanLin = -(C * M⁻¹ * Cᴴ - 1).toEuclideanLin := by
    rw [show (1 : Matrix n n ℂ) - C * M⁻¹ * Cᴴ = -(C * M⁻¹ * Cᴴ - 1) by abel]
    exact map_neg _ _
  have hform (x : WithLp 2 (EuclideanSpace ℂ m × EuclideanSpace ℂ n)) :=
    congrArg Complex.re (electricMagneticSchurEquiv_form C M hM.1 x)
  simp only [he, hb, Matrix.toLpLin_one] at hform
  have hp : ∀ i, 0 < hMs.eigenvalues rfl i := positive_matrix_eigenvalues M hM hMs
  have hc₀ := positive_schur_negative_count
    (Cᴴ * C - M).toEuclideanLin (C * M⁻¹ * Cᴴ - 1).toEuclideanLin M.toEuclideanLin
    hE hB hMs
  have hc₁ := hc₀ hp
  have hc₂ := hc₁ (electricMagneticSchurEquiv C M)
  have hc := hc₂ hform
  simpa only [finrank_euclideanSpace] using hc

/-- The actual Yee electric and magnetic spaces have equal cardinality,
so their full negative inertia is identical. -/
theorem electric_magnetic_negative_count_eq
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) (hM : M.PosDef)
    (hdim : Fintype.card m = Fintype.card n)
    (hE : (Cᴴ * C - M).toEuclideanLin.IsSymmetric)
    (hB : (C * M⁻¹ * Cᴴ - 1).toEuclideanLin.IsSymmetric) :
    (Finset.univ.filter fun i => hE.eigenvalues rfl i < 0).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < 0).card := by
  have h := electric_magnetic_negative_count C M hM hE hB
  omega

omit [Fintype n] in
/-- Exact normalization between the unit-threshold magnetic complement and
the physical magnetic operator with threshold `t`. -/
theorem scaled_magnetic_identity
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) (hM : IsUnit M)
    (t : ℂ) (ht : t ≠ 0) :
    t • (C * (t • M)⁻¹ * Cᴴ - 1) = C * M⁻¹ * Cᴴ - t • 1 := by
  let : Invertible t := invertibleOfNonzero ht
  rw [Matrix.inv_smul M t (M.isUnit_iff_isUnit_det.mp hM)]
  simp only [invOf_eq_inv, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul,
    mul_inv_cancel₀ ht, one_smul]

omit [Fintype n] in
theorem scaled_magnetic_identity_real
    (C : Matrix n m ℂ) (M : Matrix m m ℂ) (hM : IsUnit M)
    (t : ℝ) (ht : t ≠ 0) :
    t • (C * (t • M)⁻¹ * Cᴴ - 1) = C * M⁻¹ * Cᴴ - t • 1 := by
  have hinv : (t • M)⁻¹ = t⁻¹ • M⁻¹ := Matrix.inv_eq_left_inv (by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul _ (M.isUnit_iff_isUnit_det.mp hM), mul_inv_cancel₀ ht, one_smul])
  rw [hinv]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul,
    mul_inv_cancel₀ ht, one_smul]

theorem toEuclideanLin_real_smul (A : Matrix m m ℂ) (t : ℝ) :
    (t • A).toEuclideanLin = t • A.toEuclideanLin := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]

end Matrix

end Maxwell.Spectral
