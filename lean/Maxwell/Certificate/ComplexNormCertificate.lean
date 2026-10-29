import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace Maxwell.Certificate.ComplexNormCertificate

open Matrix
open scoped ComplexOrder

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Euclidean continuous linear map of a possibly rectangular matrix. -/
def rectangularOperator (F : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  F.toEuclideanLin.toContinuousLinearMap

omit [Fintype n] [DecidableEq n] in
theorem posSemidef_of_positive_smul (A : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (h : (a • A).PosSemidef) : A.PosSemidef := by
  have hh := h.smul (inv_nonneg.mpr ha.le)
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using hh

theorem quadratic_upper (H : Matrix n n ℂ) (C : ℝ)
    (h : ((C : ℂ) • (1 : Matrix n n ℂ) - H).PosSemidef)
    (x : EuclideanSpace ℂ n) :
    Complex.re (inner ℂ x (H.toEuclideanLin x)) ≤ C * ‖x‖^2 := by
  have hh := (Matrix.isPositive_toEuclideanLin_iff.mpr h).re_inner_nonneg_right x
  simp only [map_sub, map_smul, Matrix.toLpLin_one, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, inner_smul_right,
    map_sub, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  have hn : Complex.re (inner ℂ x x) = ‖x‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  rw [hn] at hh
  linarith

theorem gram_quadratic (F : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    Complex.re (inner ℂ x ((F.conjTranspose * F).toEuclideanLin x)) =
      ‖rectangularOperator F x‖^2 := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [show Matrix.toLpLin 2 2 F.conjTranspose = F.toEuclideanLin.adjoint from
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint F, LinearMap.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

/-- A finite complex Gram certificate controls the actual Euclidean operator
norm, including rectangular matrices. -/
theorem rectangular_norm_le_of_gram (F : Matrix m n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : (((C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - F.conjTranspose * F).PosSemidef) :
    ‖rectangularOperator F‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hx := quadratic_upper (F.conjTranspose * F) (C^2) h x
  rw [gram_quadratic] at hx
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  nlinarith only [hx]

theorem norm_le_of_gram (F : Matrix n n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : (((C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - F.conjTranspose * F).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) F‖ ≤ C :=
  rectangular_norm_le_of_gram F C hC h

/-- Positive power-of-two scaling of the Gram check does not alter its
operator-norm conclusion. The scale can remain in the accepted matrix. -/
theorem rectangular_norm_le_of_scaled_gram (F : Matrix m n ℂ) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 < a)
    (h : (a • (((C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) -
      F.conjTranspose * F)).PosSemidef) :
    ‖rectangularOperator F‖ ≤ C :=
  rectangular_norm_le_of_gram F C hC (posSemidef_of_positive_smul _ a ha h)

theorem norm_le_of_scaled_gram (F : Matrix n n ℂ) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (h : (a • (((C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) -
      F.conjTranspose * F)).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) F‖ ≤ C :=
  rectangular_norm_le_of_scaled_gram F C a hC ha h

theorem rectangular_norm_le_of_scaled_difference (F : Matrix m n ℂ) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 < a)
    (h : ((((a*C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) -
      a • (F.conjTranspose * F)).PosSemidef) :
    ‖rectangularOperator F‖ ≤ C := by
  apply rectangular_norm_le_of_scaled_gram F C a hC ha
  convert h using 1
  rw [smul_sub, ← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul]

/-- Two-sided Hermitian form certificates control the Euclidean operator
norm with the same constant, without an entrywise dimension factor. -/
theorem hermitian_norm_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (C : ℝ) (hC : 0 ≤ C)
    (hlo : ((C : ℂ) • (1 : Matrix n n ℂ) + H).PosSemidef)
    (hhi : ((C : ℂ) • (1 : Matrix n n ℂ) - H).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H‖ ≤ C := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  change ‖T‖ ≤ C
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.rayleighQuotient, hC]
  have hnorm : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hu := quadratic_upper H C hhi x
  have hl := quadratic_upper (-H) C (by simpa only [sub_neg_eq_add] using hlo) x
  simp only [map_neg, LinearMap.neg_apply, inner_neg_right, map_neg] at hl
  change -Complex.re (inner ℂ x (H.toEuclideanLin x)) ≤ C*‖x‖^2 at hl
  change |Complex.re (inner ℂ (T x) x) / ‖x‖^2| ≤ C
  have hswap : Complex.re (inner ℂ (T x) x) = Complex.re (inner ℂ x (T x)) :=
    inner_re_symm (𝕜 := ℂ) (T x) x
  rw [hswap, abs_div, abs_of_pos hnorm, div_le_iff₀ hnorm]
  change |Complex.re (inner ℂ x (H.toEuclideanLin x))| ≤ C*‖x‖^2
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem hermitian_norm_le_of_scaled (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hlo : (a • ((C : ℂ) • (1 : Matrix n n ℂ) + H)).PosSemidef)
    (hhi : (a • ((C : ℂ) • (1 : Matrix n n ℂ) - H)).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H‖ ≤ C :=
  hermitian_norm_le H hH C hC (posSemidef_of_positive_smul _ a ha hlo)
    (posSemidef_of_positive_smul _ a ha hhi)

def columnsMatrix (v : n → EuclideanSpace ℂ m) : Matrix m n ℂ := fun i j => v j i

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem columns_gram (v : n → EuclideanSpace ℂ m) (i j : n) :
    ((columnsMatrix v).conjTranspose * columnsMatrix v) i j =
      inner ℂ (v i) (v j) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, columnsMatrix, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem rectangularOperator_columns_apply (v : n → EuclideanSpace ℂ m)
    (x : EuclideanSpace ℂ n) :
    rectangularOperator (columnsMatrix v) x = ∑ j, x j • v j := by
  ext i
  change ((columnsMatrix v) *ᵥ WithLp.ofLp x) i = _
  simp [columnsMatrix, Matrix.mulVec, dotProduct, mul_comm]

/-- A scaled finite Gram certificate of the actual columns bounds every
complex linear combination in the Euclidean coefficient norm. -/
theorem synthesis_bound_of_scaled_gram (v : n → EuclideanSpace ℂ m) (G : Matrix n n ℂ)
    (hG : ∀ i j, G i j = inner ℂ (v i) (v j)) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (h : (a • (((C^2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) - G)).PosSemidef)
    (x : EuclideanSpace ℂ n) : ‖∑ j, x j • v j‖ ≤ C*‖x‖ := by
  have hgram : (columnsMatrix v).conjTranspose * columnsMatrix v = G := by
    ext i j
    exact (columns_gram v i j).trans (hG i j).symm
  have hnorm := rectangular_norm_le_of_scaled_gram (columnsMatrix v) C a hC ha
    (by simpa only [hgram] using h)
  rw [← rectangularOperator_columns_apply]
  exact (ContinuousLinearMap.le_opNorm _ x).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))

end
end Maxwell.Certificate.ComplexNormCertificate
