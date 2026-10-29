import Maxwell.Composition.RectangularSaddle
import Maxwell.Algebra

/-! The rectangular Hilbert-space saddle estimates apply to the literal
sparse block matrix emitted by the reduction. -/
noncomputable section
namespace Maxwell.Composition.RectangularSaddle
open Matrix
open scoped InnerProduct
set_option maxHeartbeats 800000
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def sumPair : EuclideanSpace ℝ (ι ⊕ κ) ≃ₗᵢ[ℝ]
    Pair (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ) :=
  PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι ⊕ κ => ℝ)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem sumPair_fst (x : EuclideanSpace ℝ (ι ⊕ κ)) (i : ι) :
    (sumPair x).fst i = x (Sum.inl i) := rfl
omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem sumPair_snd (x : EuclideanSpace ℝ (ι ⊕ κ)) (j : κ) :
    (sumPair x).snd j = x (Sum.inr j) := rfl

theorem rectangular_adjoint (A : Matrix ι κ ℝ) :
    (rectangularEuclideanCLM A).adjoint = rectangularEuclideanCLM A.transpose := by
  unfold rectangularEuclideanCLM
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [conjTranspose_eq_transpose_of_trivial]

def matrix (A : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks 1 A A.transpose 0

theorem matrix_intertwine (A : Matrix ι κ ℝ) (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    sumPair (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) x) =
      saddle (rectangularEuclideanCLM A) (sumPair x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · ext i
    change (matrix A).mulVec x (Sum.inl i) = x (Sum.inl i) + _
    simp [matrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      rectangularEuclideanCLM_apply, Matrix.one_apply]
  · ext j
    change (matrix A).mulVec x (Sum.inr j) =
      (rectangularEuclideanCLM A).adjoint (sumPair x).fst j
    rw [rectangular_adjoint]
    simp [matrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      rectangularEuclideanCLM_apply]

def matrixEquiv (A : Matrix ι κ ℝ) (hA : Function.Injective (rectangularEuclideanCLM A)) :
    EuclideanSpace ℝ (ι ⊕ κ) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
  sumPair.toContinuousLinearEquiv.trans
    ((saddleEquiv (rectangularEuclideanCLM A) hA).trans sumPair.symm.toContinuousLinearEquiv)

theorem matrixEquiv_operator (A : Matrix ι κ ℝ) (hA : Function.Injective (rectangularEuclideanCLM A)) :
    (matrixEquiv A hA : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ)) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply sumPair.injective
  change sumPair (sumPair.symm (saddle (rectangularEuclideanCLM A) (sumPair x))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, matrix_intertwine]

theorem matrix_norm_le (A : Matrix ι κ ℝ) (hA : ‖rectangularEuclideanCLM A‖ ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [← sumPair.norm_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) x), matrix_intertwine]
  exact ((saddle (rectangularEuclideanCLM A)).le_opNorm _).trans
    (by simpa only [sumPair.norm_map] using
      mul_le_mul_of_nonneg_right (saddle_norm_le _ hA) (norm_nonneg (sumPair x)))

theorem matrix_inverse_norm_le (A : Matrix ι κ ℝ)
    (hA : Function.Injective (rectangularEuclideanCLM A))
    (L : ℝ) (hL : 1 ≤ L) (hlower : ∀ x, ‖x‖ ≤ L*‖rectangularEuclideanCLM A x‖) :
    ‖((matrixEquiv A hA).symm : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ]
      EuclideanSpace ℝ (ι ⊕ κ))‖ ≤ 4*L^2 := by
  let e := sumPair (ι := ι) (κ := κ)
  let T := saddleEquiv (rectangularEuclideanCLM A) hA
  have hT : ‖(T.symm : Pair (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ) →L[ℝ]
      Pair (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ))‖ ≤ 4*L^2 :=
    saddle_inverse_norm_le _ hA L hL hlower
  have hl (x : EuclideanSpace ℝ (ι ⊕ κ)) :
      ‖x‖ ≤ 4*L^2*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) x‖ := by
    have hh := ((T.symm : Pair (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ) →L[ℝ]
      Pair (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ)).le_opNorm (T (e x))).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (T (e x))))
    change ‖T.symm (T (e x))‖ ≤ 4*L^2*‖T (e x)‖ at hh
    rw [T.symm_apply_apply, e.norm_map] at hh
    have hi : T (e x) = e (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) x) :=
      (matrix_intertwine A x).symm
    rw [hi, e.norm_map] at hh
    exact hh
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hh := hl ((matrixEquiv A hA).symm x)
  have hc : Matrix.toEuclideanCLM (𝕜 := ℝ) (matrix A) ((matrixEquiv A hA).symm x) = x := by
    rw [← matrixEquiv_operator A hA]
    exact (matrixEquiv A hA).apply_symm_apply x
  rw [hc] at hh
  exact hh

end Maxwell.Composition.RectangularSaddle
