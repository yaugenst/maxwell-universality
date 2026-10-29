import Maxwell.Composition.SignedMediator

/-! Euclidean block inversion and arbitrary-residual transfer for subdivision.
The full inverse is constructed from the internal and Schur inverses. -/

noncomputable section
namespace Maxwell.Composition.SubdivisionOperator

open Matrix
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def operator (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ) :
    EuclideanSpace ℝ (V ⊕ I) →L[ℝ] EuclideanSpace ℝ (V ⊕ I) :=
  Matrix.toEuclideanCLM (n := V ⊕ I) (𝕜 := ℝ) (Matrix.fromBlocks A C C.transpose D)

def schurMatrix (A : Matrix V V ℝ) (C : Matrix V I ℝ) (Di : Matrix I I ℝ) :
    Matrix V V ℝ := A - C * Di * C.transpose

theorem upper_left (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ) :
    sumLeftProjection.comp ((operator A C D).comp sumLeftInjection) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) A := by
  ext x i
  change (Matrix.fromBlocks A C C.transpose D *ᵥ
    Sum.elim (WithLp.ofLp x) (0 : I → ℝ)) (Sum.inl i) = _
  simp [Matrix.fromBlocks_mulVec]

theorem upper_right (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ) :
    sumLeftProjection.comp ((operator A C D).comp sumRightInjection) =
      Maxwell.rectangularEuclideanCLM C := by
  ext x i
  change (Matrix.fromBlocks A C C.transpose D *ᵥ
    Sum.elim (0 : V → ℝ) (WithLp.ofLp x)) (Sum.inl i) = (C *ᵥ WithLp.ofLp x) i
  simp [Matrix.fromBlocks_mulVec]

theorem lower_left (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ) :
    sumRightProjection.comp ((operator A C D).comp sumLeftInjection) =
      Maxwell.rectangularEuclideanCLM C.transpose := by
  ext x i
  change (Matrix.fromBlocks A C C.transpose D *ᵥ
    Sum.elim (WithLp.ofLp x) (0 : I → ℝ)) (Sum.inr i) = (C.transpose *ᵥ WithLp.ofLp x) i
  simp [Matrix.fromBlocks_mulVec]

theorem lower_right (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ) :
    sumRightProjection.comp ((operator A C D).comp sumRightInjection) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D := by
  ext x i
  change (Matrix.fromBlocks A C C.transpose D *ᵥ
    Sum.elim (0 : V → ℝ) (WithLp.ofLp x)) (Sum.inr i) = _
  simp [Matrix.fromBlocks_mulVec]

theorem operator_schur (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di) :
    brightSchurOperator (operator A C D) sumLeftInjection sumRightInjection
      sumLeftProjection sumRightProjection Dc =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di) := by
  rw [brightSchurOperator, upper_left, upper_right, lower_left, hDi]
  have hp := rectangularEuclideanCLM_mul (C * Di) C.transpose
  conv_rhs at hp => rw [rectangularEuclideanCLM_mul, rectangularEuclideanCLM_square,
    ContinuousLinearMap.comp_assoc]
  rw [← hp, rectangularEuclideanCLM_square, ← map_sub]
  rfl

/-- Only the two local block equivalences are premises; the full block
operator is inverted by the common-space complementary construction. -/
def equiv (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di)) :
    EuclideanSpace ℝ (V ⊕ I) ≃L[ℝ] EuclideanSpace ℝ (V ⊕ I) :=
  complementaryEquiv (operator A C D) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc S sumCoordinate_decomposition
    (fun c => by
      have h := congrArg (fun F => F c) (lower_right A C D)
      simpa only [ContinuousLinearMap.comp_apply, ← hDc,
        ContinuousLinearEquiv.coe_coe] using h)
    (by rw [operator_schur A C D Di Dc hDi, hS])
    sumLeftProjection_left sumLeftProjection_right sumRightProjection_left sumRightProjection_right

@[simp] theorem equiv_coe (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di)) :
    (equiv A C D Di Dc S hDc hDi hS :
      EuclideanSpace ℝ (V ⊕ I) →L[ℝ] EuclideanSpace ℝ (V ⊕ I)) = operator A C D := rfl

theorem mixed_left_norm_le (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I) (ell : ℝ) (hell : 0 ≤ ell)
    (hCt : ‖Maxwell.rectangularEuclideanCLM C.transpose‖ ≤ 2)
    (hDinorm : ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ ell) :
    ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I).comp
      (sumRightProjection.comp ((operator A C D).comp sumLeftInjection))‖ ≤ 2 * ell := by
  rw [lower_left]
  calc
    _ ≤ ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ *
        ‖Maxwell.rectangularEuclideanCLM C.transpose‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ell * 2 := mul_le_mul hDinorm hCt (norm_nonneg _) hell
    _ = _ := mul_comm _ _

theorem mixed_right_norm_le (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I) (ell : ℝ)
    (hC : ‖Maxwell.rectangularEuclideanCLM C‖ ≤ 2)
    (hDinorm : ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ ell) :
    ‖(sumLeftProjection.comp ((operator A C D).comp sumRightInjection)).comp
      (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ 2 * ell := by
  rw [upper_right]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hC hDinorm (norm_nonneg _) (by norm_num))

theorem inverse_norm_le (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di))
    (ell Q : ℝ) (hell : 0 ≤ ell)
    (hC : ‖Maxwell.rectangularEuclideanCLM C‖ ≤ 2)
    (hCt : ‖Maxwell.rectangularEuclideanCLM C.transpose‖ ≤ 2)
    (hDinorm : ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ ell)
    (hSnorm : ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Q) :
    ‖((equiv A C D Di Dc S hDc hDi hS).symm :
      EuclideanSpace ℝ (V ⊕ I) →L[ℝ] EuclideanSpace ℝ (V ⊕ I))‖ ≤
      (1 + 2 * ell) ^ 2 * Q + ell := by
  change ‖complementaryInverse (operator A C D) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc S‖ ≤ _
  have h := complementaryInverse_norm_le_of_local_bounds (operator A C D)
    sumLeftInjection sumRightInjection sumLeftProjection sumRightProjection Dc S
    (2 * ell) (2 * ell) sumLeftInjection_norm_le sumRightInjection_norm_le
    sumLeftProjection_norm_le sumRightProjection_norm_le
    (mixed_left_norm_le A C D Dc ell hell hCt hDinorm)
    (mixed_right_norm_le A C D Dc ell hC hDinorm)
  calc
    _ ≤ (1 + 2 * ell) * (1 + 2 * ell) *
        ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ +
        ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ := h
    _ ≤ (1 + 2 * ell) * (1 + 2 * ell) * Q + ell := by gcongr
    _ = _ := by ring

theorem polynomial_bound (ell Q : ℝ) (hell : 1 ≤ ell) (hQ : 0 ≤ Q) :
    (1 + 2 * ell) ^ 2 * Q + ell ≤ 9 * ell ^ 2 * (Q + ell) := by
  have hell0 : 0 ≤ ell := by linarith
  have hs : (1 + 2 * ell) ^ 2 ≤ 9 * ell ^ 2 := by nlinarith
  have he2 : 1 ≤ ell ^ 2 := by nlinarith
  have he3 := mul_le_mul_of_nonneg_right he2 hell0
  have hsqQ := mul_le_mul_of_nonneg_right hs hQ
  nlinarith [mul_nonneg (sq_nonneg ell) hell0]

theorem inverse_norm_le_polynomial
    (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di))
    (ell Q : ℝ) (hell : 1 ≤ ell)
    (hC : ‖Maxwell.rectangularEuclideanCLM C‖ ≤ 2)
    (hCt : ‖Maxwell.rectangularEuclideanCLM C.transpose‖ ≤ 2)
    (hDinorm : ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ ell)
    (hSnorm : ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Q) :
    ‖((equiv A C D Di Dc S hDc hDi hS).symm :
      EuclideanSpace ℝ (V ⊕ I) →L[ℝ] EuclideanSpace ℝ (V ⊕ I))‖ ≤
      9 * ell ^ 2 * (Q + ell) :=
  (inverse_norm_le A C D Di Dc S hDc hDi hS ell Q (by linarith)
    hC hCt hDinorm hSnorm).trans
      (polynomial_bound ell Q hell ((norm_nonneg _).trans hSnorm))

/-- Exact elimination keeps every internal residual component. -/
theorem residual_identity (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (z : EuclideanSpace ℝ (V ⊕ I)) (g : EuclideanSpace ℝ V) :
    (Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di))
      (sumLeftProjection z) - g =
      complementaryResidualMap (operator A C D) sumRightInjection sumLeftProjection
        sumRightProjection Dc (operator A C D z - sumLeftInjection g) := by
  have h := complementary_schur_residual (operator A C D) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc sumCoordinate_decomposition
    (fun c => by
      have hh := congrArg (fun F => F c) (lower_right A C D)
      simpa only [ContinuousLinearMap.comp_apply, ← hDc,
        ContinuousLinearEquiv.coe_coe] using hh)
    sumLeftProjection_left sumRightProjection_left z g
    (operator A C D z - sumLeftInjection g) (by abel)
  rw [operator_schur A C D Di Dc hDi] at h
  rw [h]
  abel

/-- The bound holds for every supplied full vector and terminal source. -/
theorem residual_transfer (A : Matrix V V ℝ) (C : Matrix V I ℝ) (D Di : Matrix I I ℝ)
    (Dc : EuclideanSpace ℝ I ≃L[ℝ] EuclideanSpace ℝ I)
    (hDc : (Dc : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) D)
    (hDi : (Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Di)
    (ell : ℝ) (hC : ‖Maxwell.rectangularEuclideanCLM C‖ ≤ 2)
    (hDinorm : ‖(Dc.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖ ≤ ell)
    (z : EuclideanSpace ℝ (V ⊕ I)) (g : EuclideanSpace ℝ V) :
    ‖(Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (schurMatrix A C Di))
      (sumLeftProjection z) - g‖ ≤ (1 + 2 * ell) *
        ‖operator A C D z - sumLeftInjection g‖ := by
  rw [residual_identity A C D Di Dc hDc hDi]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact complementaryResidualMap_norm_le (operator A C D) sumRightInjection
    sumLeftProjection sumRightProjection Dc (2 * ell)
    sumLeftProjection_norm_le sumRightProjection_norm_le
    (mixed_right_norm_le A C D Dc ell hC hDinorm)

end Maxwell.Composition.SubdivisionOperator
