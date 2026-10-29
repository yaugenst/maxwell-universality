import Maxwell.Algebra
import Maxwell.Composition.Complement
import Maxwell.Composition.Mediator
import Maxwell.Composition.BlockModes
import Maxwell.Composition.SumCoordinates
import Maxwell.SchurBound
import Mathlib.Tactic.FieldSimp

/-!
# Concrete signed mediator assembly

Every mediator has two distinct terminal endpoints and one logical sign.
The matrices are assembled from these incidences; their Schur complement
is proved entry by entry rather than supplied as a hypothesis.
-/

noncomputable section

namespace Maxwell.Composition

open Matrix
open scoped BigOperators

theorem rectangularEuclideanCLM_mul {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (A : Matrix X Y ℝ) (B : Matrix Y Z ℝ) :
    Maxwell.rectangularEuclideanCLM (A * B) =
      (Maxwell.rectangularEuclideanCLM A).comp (Maxwell.rectangularEuclideanCLM B) := by
  ext x i
  change ((A * B) *ᵥ (WithLp.ofLp x)) i = (A *ᵥ (B *ᵥ WithLp.ofLp x)) i
  rw [Matrix.mulVec_mulVec]

theorem rectangularEuclideanCLM_square {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) :
    Maxwell.rectangularEuclideanCLM A = Matrix.toEuclideanCLM (n := X) (𝕜 := ℝ) A := rfl

/-- Finite endpoint data for a loop-free signed graph; parallel edges are
allowed and contribute separately to degree and adjacency. -/
structure SignedIncidence (V E : Type*) where
  tail : E → V
  head : E → V
  distinct : ∀ e, tail e ≠ head e
  sign : E → ℝ
  abs_sign : ∀ e, |sign e| = 1

namespace SignedIncidence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (G : SignedIncidence V E)

def incidence : Matrix V E ℝ := fun i e =>
  if i = G.tail e then 1 else if i = G.head e then G.sign e else 0

def degree (i : V) : ℝ := ∑ e, if i = G.tail e ∨ i = G.head e then 1 else 0

def adjacency : Matrix V V ℝ := fun i j => ∑ e,
  ((if i = G.tail e ∧ j = G.head e then G.sign e else 0) +
  (if i = G.head e ∧ j = G.tail e then G.sign e else 0))

def logicalMatrix (diag : V → ℝ) : Matrix V V ℝ := Matrix.diagonal diag + G.adjacency

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem sign_sq (e : E) : G.sign e ^ 2 = 1 := by
  have h := congrArg (fun x : ℝ => x ^ 2) (G.abs_sign e)
  simpa only [sq_abs, one_pow] using h

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem abs_incidence (i : V) (e : E) :
    |G.incidence i e| = if i = G.tail e ∨ i = G.head e then 1 else 0 := by
  by_cases ht : i = G.tail e
  · simp [incidence, ht]
  · by_cases hh : i = G.head e
    · simp only [incidence, ite_eq_right ht, ite_eq_left hh, G.abs_sign,
        ite_eq_left (Or.inr hh)]
    · simp [incidence, ht, hh]

omit [Fintype V] [DecidableEq E] in
theorem incidence_row_sum (i : V) : ∑ e, |G.incidence i e| = G.degree i := by
  simp only [abs_incidence, degree]

omit [Fintype E] [DecidableEq E] in
theorem incidence_column_sum (e : E) : ∑ i, |G.incidence i e| = 2 := by
  have hpoint (i : V) : |G.incidence i e| =
      (if i = G.tail e then 1 else 0) + (if i = G.head e then 1 else 0) := by
    rw [abs_incidence]
    by_cases ht : i = G.tail e
    · simp [ht, G.distinct e]
    · by_cases hh : i = G.head e <;> simp [ht, hh, Ne.symm (G.distinct e)]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  norm_num

omit [Fintype V] [DecidableEq E] in
/-- The Gram matrix of signed incidences is degree plus signed adjacency. -/
theorem incidence_gram : G.incidence * G.incidence.transpose =
    Matrix.diagonal G.degree + G.adjacency := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, adjacency]
  have hpoint (e : E) : G.incidence i e * G.incidence j e =
      (if i = j then (if i = G.tail e ∨ i = G.head e then 1 else 0) else 0) +
      ((if i = G.tail e ∧ j = G.head e then G.sign e else 0) +
       (if i = G.head e ∧ j = G.tail e then G.sign e else 0)) := by
    have hneq := G.distinct e
    have hsq := G.sign_sq e
    by_cases hit : i = G.tail e <;> by_cases hih : i = G.head e <;>
      by_cases hjt : j = G.tail e <;> by_cases hjh : j = G.head e <;>
      by_cases hij : i = j <;>
      simp_all [incidence, sq]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases hij : i = j <;> simp [degree, hij]

/-- Each edge uses the calibrated physical axial magnitude on both incidences;
its logical sign occurs on the head incidence. -/
def coupling (β : E → ℝ) : Matrix V E ℝ := fun i e => G.incidence i e * β e

def mediatorDiagonal (α : ℝ) (β : E → ℝ) : Matrix E E ℝ :=
  Matrix.diagonal fun e => -(β e ^ 2) / α

def mediatorInverse (α : ℝ) (β : E → ℝ) : Matrix E E ℝ :=
  Matrix.diagonal fun e => -α / (β e ^ 2)

def terminalDiagonal (α : ℝ) (diag : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal fun i => α * (diag i - G.degree i)

def targetMatrix (α : ℝ) (β : E → ℝ) (diag : V → ℝ) : Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  Matrix.fromBlocks (G.terminalDiagonal α diag) (G.coupling β)
    (G.coupling β).transpose (mediatorDiagonal α β)

theorem mediator_inverse_mul (α : ℝ) (β : E → ℝ) (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    mediatorInverse α β * mediatorDiagonal α β = 1 := by
  rw [mediatorInverse, mediatorDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    field_simp [hβ i]
  · simp [hij]

theorem mediator_mul_inverse (α : ℝ) (β : E → ℝ) (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    mediatorDiagonal α β * mediatorInverse α β = 1 := by
  rw [mediatorDiagonal, mediatorInverse, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    field_simp [hβ i]
  · simp [hij]

omit [Fintype V] in
theorem coupling_inverse_entry (α : ℝ) (β : E → ℝ)
    (i : V) (e : E) :
    (G.coupling β * mediatorInverse α β) i e =
      -(α / β e) * G.incidence i e := by
  rw [mediatorInverse, Matrix.mul_diagonal]
  dsimp [coupling]
  field_simp

omit [Fintype V] in
/-- The actual two-incidence assembly has exactly the signed target Schur
complement, including every diagonal degree correction. -/
theorem target_schur (α : ℝ) (β : E → ℝ) (diag : V → ℝ) (hβ : ∀ e, β e ≠ 0) :
    G.terminalDiagonal α diag - G.coupling β * mediatorInverse α β *
      (G.coupling β).transpose = α • G.logicalMatrix diag := by
  have hproduct : G.coupling β * mediatorInverse α β * (G.coupling β).transpose =
      -α • (G.incidence * G.incidence.transpose) := by
    ext i j
    change (∑ e, (G.coupling β * mediatorInverse α β) i e * G.coupling β j e) =
      -α * ∑ e, G.incidence i e * G.incidence j e
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [coupling_inverse_entry]
    dsimp [coupling]
    field_simp [hβ e]
  rw [hproduct, incidence_gram]
  ext i j
  by_cases hij : i = j
  · simp [terminalDiagonal, logicalMatrix, hij]
    ring
  · simp [terminalDiagonal, logicalMatrix, hij]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem coupling_ne_zero (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (e : E) : β e ≠ 0 := by
  apply abs_pos.mp
  linarith [hβ e]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem inverse_ratio_le (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (e : E) : |α / β e| ≤ (1 : ℝ) / 3 := by
  have hb : 0 < |β e| := abs_pos.mpr (coupling_ne_zero α β hα hβ e)
  rw [abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hb).mpr
  linarith [hβ e]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem mediator_inverse_scalar_bound (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (e : E) : |-α / (β e ^ 2)| ≤ 1 / α := by
  have hb := coupling_ne_zero α β hα hβ e
  have hb2 : 0 < β e ^ 2 := sq_pos_of_ne_zero hb
  rw [abs_div, abs_neg, abs_of_pos hα, abs_of_pos hb2]
  apply (div_le_div_iff₀ hb2 hα).mpr
  have hm := hβ e
  have hs := sq_abs (β e)
  have ha : α ≤ |β e| := by linarith
  have hh := mul_self_le_mul_self hα.le ha
  nlinarith

/-- The inverse diagonal has the claimed Euclidean norm, independently of
the mediator count. -/
theorem mediator_inverse_norm_le (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) :
    ‖Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorInverse α β)‖ ≤ 1 / α := by
  apply Maxwell.matrix_toEuclideanCLM_norm_le _ _ (by positivity)
  · intro e
    simpa [mediatorInverse, Matrix.diagonal_apply, apply_ite abs] using
      mediator_inverse_scalar_bound α β hα hβ e
  · intro e
    simpa [mediatorInverse, Matrix.diagonal_apply, apply_ite abs] using
      mediator_inverse_scalar_bound α β hα hβ e

omit [Fintype V] in
theorem coupling_inverse_row_bound (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3) (i : V) :
    ∑ e, |(G.coupling β * mediatorInverse α β) i e| ≤ 1 := by
  calc
    _ ≤ ∑ e, ((1 : ℝ) / 3) * |G.incidence i e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [coupling_inverse_entry, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (inverse_ratio_le α β hα hβ e) (abs_nonneg _)
    _ = ((1 : ℝ) / 3) * G.degree i := by rw [← Finset.mul_sum, incidence_row_sum]
    _ ≤ 1 := by linarith [hdeg i]

theorem coupling_inverse_column_bound (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (e : E) :
    ∑ i, |(G.coupling β * mediatorInverse α β) i e| ≤ 1 := by
  calc
    _ ≤ ∑ i, ((1 : ℝ) / 3) * |G.incidence i e| := by
      apply Finset.sum_le_sum
      intro i _
      rw [coupling_inverse_entry, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (inverse_ratio_le α β hα hβ e) (abs_nonneg _)
    _ = ((1 : ℝ) / 3) * 2 := by rw [← Finset.mul_sum, incidence_column_sum]
    _ ≤ 1 := by norm_num

/-- The paper's axial magnitude margin gives a stronger bound than
`sqrt 6`: both mixed inverse products are contractions. -/
theorem coupling_inverse_norm_le (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (G.coupling β * mediatorInverse α β)‖ ≤ 1 :=
  Maxwell.rectangularEuclideanCLM_norm_le _ _ zero_le_one
    (G.coupling_inverse_row_bound α β hα hβ hdeg)
    (G.coupling_inverse_column_bound α β hα hβ)

theorem inverse_coupling_transpose_norm_le (α : ℝ) (β : E → ℝ) (hα : 0 < α)
    (hβ : ∀ e, 3 * α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (mediatorInverse α β * (G.coupling β).transpose)‖ ≤ 1 := by
  have hid : mediatorInverse α β * (G.coupling β).transpose =
      (G.coupling β * mediatorInverse α β).transpose := by
    rw [Matrix.transpose_mul]
    simp [mediatorInverse]
  rw [hid]
  apply Maxwell.rectangularEuclideanCLM_norm_le _ _ zero_le_one
  · exact G.coupling_inverse_column_bound α β hα hβ
  · exact G.coupling_inverse_row_bound α β hα hβ hdeg

/-- Continuous inverse of the actual diagonal mediator block. -/
def mediatorEquiv (α : ℝ) (β : E → ℝ) (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    EuclideanSpace ℝ E ≃L[ℝ] EuclideanSpace ℝ E :=
  ContinuousLinearEquiv.equivOfInverse'
    (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorDiagonal α β))
    (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorInverse α β))
    (by
      change (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorDiagonal α β)) *
        (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorInverse α β)) = 1
      rw [← map_mul, mediator_mul_inverse α β hα hβ, map_one])
    (by
      change (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorInverse α β)) *
        (Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorDiagonal α β)) = 1
      rw [← map_mul, mediator_inverse_mul α β hα hβ, map_one])

@[simp] theorem mediatorEquiv_coe (α : ℝ) (β : E → ℝ) (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    (mediatorEquiv α β hα hβ : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E) =
      Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorDiagonal α β) := rfl

@[simp] theorem mediatorEquiv_symm_coe (α : ℝ) (β : E → ℝ) (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    ((mediatorEquiv α β hα hβ).symm : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E) =
      Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorInverse α β) := rfl

def targetOperator (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    EuclideanSpace ℝ (V ⊕ E) →L[ℝ] EuclideanSpace ℝ (V ⊕ E) :=
  Matrix.toEuclideanCLM (n := V ⊕ E) (𝕜 := ℝ) (G.targetMatrix α β diag)

theorem target_upper_left (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    sumLeftProjection.comp ((G.targetOperator α β diag).comp sumLeftInjection) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.terminalDiagonal α diag) := by
  ext x i
  change (G.targetMatrix α β diag *ᵥ Sum.elim (WithLp.ofLp x) (0 : E → ℝ)) (Sum.inl i) =
    (G.terminalDiagonal α diag *ᵥ WithLp.ofLp x) i
  simp [targetMatrix, Matrix.fromBlocks_mulVec]

theorem target_upper_right (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    sumLeftProjection.comp ((G.targetOperator α β diag).comp sumRightInjection) =
      Maxwell.rectangularEuclideanCLM (G.coupling β) := by
  ext x i
  change (G.targetMatrix α β diag *ᵥ Sum.elim (0 : V → ℝ) (WithLp.ofLp x)) (Sum.inl i) =
    (G.coupling β *ᵥ WithLp.ofLp x) i
  simp [targetMatrix, Matrix.fromBlocks_mulVec]

theorem target_lower_left (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    sumRightProjection.comp ((G.targetOperator α β diag).comp sumLeftInjection) =
      Maxwell.rectangularEuclideanCLM (G.coupling β).transpose := by
  ext x i
  change (G.targetMatrix α β diag *ᵥ Sum.elim (WithLp.ofLp x) (0 : E → ℝ)) (Sum.inr i) =
    ((G.coupling β).transpose *ᵥ WithLp.ofLp x) i
  simp [targetMatrix, Matrix.fromBlocks_mulVec]

theorem target_lower_right (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    sumRightProjection.comp ((G.targetOperator α β diag).comp sumRightInjection) =
      Matrix.toEuclideanCLM (n := E) (𝕜 := ℝ) (mediatorDiagonal α β) := by
  ext x i
  change (G.targetMatrix α β diag *ᵥ Sum.elim (0 : V → ℝ) (WithLp.ofLp x)) (Sum.inr i) =
    (mediatorDiagonal α β *ᵥ WithLp.ofLp x) i
  simp [targetMatrix, Matrix.fromBlocks_mulVec]

/-- Exact matrix Schur elimination agrees with the common-space operator
Schur complement used by the full inverse theorem. -/
theorem target_operator_schur (α : ℝ) (β : E → ℝ) (diag : V → ℝ)
    (hα : α ≠ 0) (hβ : ∀ e, β e ≠ 0) :
    brightSchurOperator (G.targetOperator α β diag) sumLeftInjection sumRightInjection
      sumLeftProjection sumRightProjection (mediatorEquiv α β hα hβ) =
      α • Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diag) := by
  rw [brightSchurOperator, target_upper_left, target_upper_right, target_lower_left,
    mediatorEquiv_symm_coe]
  have hprod := rectangularEuclideanCLM_mul (G.coupling β * mediatorInverse α β)
    (G.coupling β).transpose
  conv_rhs at hprod => rw [rectangularEuclideanCLM_mul (G.coupling β) (mediatorInverse α β),
    rectangularEuclideanCLM_square, ContinuousLinearMap.comp_assoc]
  rw [← hprod, rectangularEuclideanCLM_square, ← map_sub, target_schur G α β diag hβ, map_smul]

/-- Scaling a local logical inverse constructs the terminal Schur inverse. -/
def scaledLogicalEquiv (α : ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V) (hα : α ≠ 0) :
    EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V :=
  ContinuousLinearEquiv.equivOfInverse'
    (α • (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
    (α⁻¹ • (Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
    (by ext x; simp [smul_smul, hα])
    (by ext x; simp [smul_smul, hα])

omit [DecidableEq V] in
@[simp] theorem scaledLogicalEquiv_coe (α : ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V) (hα : α ≠ 0) :
    (scaledLogicalEquiv α Γ hα : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      α • (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) := rfl

omit [DecidableEq V] in
@[simp] theorem scaledLogicalEquiv_symm_coe (α : ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V) (hα : α ≠ 0) :
    ((scaledLogicalEquiv α Γ hα).symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      α⁻¹ • (Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) := rfl

omit [DecidableEq V] in
theorem scaledLogicalEquiv_inverse_norm_le (α Kbar : ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V) (hα : 0 < α)
    (hΓ : ‖(Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Kbar) :
    ‖((scaledLogicalEquiv α Γ hα.ne').symm :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Kbar / α := by
  rw [scaledLogicalEquiv_symm_coe, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hΓ (inv_nonneg.mpr hα.le)

/-- The physical target is invertible as a consequence of the actual
signed incidence assembly and local logical invertibility. No hypothesis
asserts invertibility or an inverse estimate for the full target. -/
theorem exists_target_equiv (α Kbar : ℝ) (β : E → ℝ) (diag : V → ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hα : 0 < α) (hβ : ∀ e, 3 * α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3)
    (hΓmatrix : (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diag))
    (hΓnorm : ‖(Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Kbar) :
    ∃ T : EuclideanSpace ℝ (V ⊕ E) ≃L[ℝ] EuclideanSpace ℝ (V ⊕ E),
      (T : EuclideanSpace ℝ (V ⊕ E) →L[ℝ] EuclideanSpace ℝ (V ⊕ E)) =
        G.targetOperator α β diag ∧
      ‖(T.symm : EuclideanSpace ℝ (V ⊕ E) →L[ℝ] EuclideanSpace ℝ (V ⊕ E))‖ ≤
        4 * (Kbar / α) + 1 / α := by
  let Dc := mediatorEquiv α β hα.ne' (coupling_ne_zero α β hα hβ)
  let S := scaledLogicalEquiv α Γ hα.ne'
  have hDc : ∀ c, sumRightProjection (G.targetOperator α β diag (sumRightInjection c)) =
      Dc c := by
    intro c
    exact congrArg (fun F : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E => F c)
      (G.target_lower_right α β diag)
  have hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      brightSchurOperator (G.targetOperator α β diag) sumLeftInjection sumRightInjection
        sumLeftProjection sumRightProjection Dc := by
    rw [target_operator_schur]
    change α • (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) = _
    rw [hΓmatrix]
  let T := complementaryEquiv (G.targetOperator α β diag) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc S sumCoordinate_decomposition hDc hS
    sumLeftProjection_left sumLeftProjection_right sumRightProjection_left sumRightProjection_right
  refine ⟨T, rfl, ?_⟩
  have hleft : ‖(Dc.symm : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E).comp
      (sumRightProjection.comp ((G.targetOperator α β diag).comp sumLeftInjection))‖ ≤ 1 := by
    dsimp only [Dc]
    rw [mediatorEquiv_symm_coe, target_lower_left, ← rectangularEuclideanCLM_square,
      ← rectangularEuclideanCLM_mul]
    exact G.inverse_coupling_transpose_norm_le α β hα hβ hdeg
  have hright : ‖(sumLeftProjection.comp ((G.targetOperator α β diag).comp sumRightInjection)).comp
      (Dc.symm : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E)‖ ≤ 1 := by
    dsimp only [Dc]
    rw [mediatorEquiv_symm_coe, target_upper_right, ← rectangularEuclideanCLM_square,
      ← rectangularEuclideanCLM_mul]
    exact G.coupling_inverse_norm_le α β hα hβ hdeg
  have hbound := complementaryInverse_norm_le_of_local_bounds (G.targetOperator α β diag)
    sumLeftInjection sumRightInjection sumLeftProjection sumRightProjection Dc S 1 1
    sumLeftInjection_norm_le sumRightInjection_norm_le
    sumLeftProjection_norm_le sumRightProjection_norm_le hleft hright
  have hSnorm := scaledLogicalEquiv_inverse_norm_le α Kbar Γ hα hΓnorm
  have hDnorm : ‖(Dc.symm : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E)‖ ≤ 1 / α :=
    mediator_inverse_norm_le α β hα hβ
  change ‖complementaryInverse (G.targetOperator α β diag) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc S‖ ≤ _
  change ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Kbar / α at hSnorm
  nlinarith

/-- The manuscript's `16 Kbar / α` bound follows with room to spare from
degree three and the axial magnitude margin. -/
theorem exists_target_equiv_paper_bound (α Kbar : ℝ) (β : E → ℝ) (diag : V → ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hα : 0 < α) (hK : 1 ≤ Kbar) (hβ : ∀ e, 3 * α ≤ |β e|)
    (hdeg : ∀ i, G.degree i ≤ 3)
    (hΓmatrix : (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diag))
    (hΓnorm : ‖(Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Kbar) :
    ∃ T : EuclideanSpace ℝ (V ⊕ E) ≃L[ℝ] EuclideanSpace ℝ (V ⊕ E),
      (T : EuclideanSpace ℝ (V ⊕ E) →L[ℝ] EuclideanSpace ℝ (V ⊕ E)) =
        G.targetOperator α β diag ∧
      ‖(T.symm : EuclideanSpace ℝ (V ⊕ E) →L[ℝ] EuclideanSpace ℝ (V ⊕ E))‖ ≤
        16 * Kbar / α := by
  obtain ⟨T, hT, hnorm⟩ := G.exists_target_equiv α Kbar β diag Γ hα hβ hdeg hΓmatrix hΓnorm
  refine ⟨T, hT, hnorm.trans ?_⟩
  apply (le_div_iff₀ hα).mpr
  have hid : (4 * (Kbar / α) + 1 / α) * α = 4 * Kbar + 1 := by
    field_simp
  rw [hid]
  linarith

/-- Every approximate solution of the assembled physical target produces
the stated logical residual, including errors in the mediator equations. -/
theorem target_residual_transfer (α : ℝ) (β : E → ℝ) (diag : V → ℝ)
    (hα : 0 < α) (hβ : ∀ e, 3 * α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3)
    (z : EuclideanSpace ℝ (V ⊕ E)) (g : EuclideanSpace ℝ V) :
    ‖(Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diag))
        (sumLeftProjection z) - g‖ ≤
      (4 / α) * ‖G.targetOperator α β diag z - α • sumLeftInjection g‖ := by
  let Dc := mediatorEquiv α β hα.ne' (coupling_ne_zero α β hα hβ)
  have hDc : ∀ c, sumRightProjection (G.targetOperator α β diag (sumRightInjection c)) =
      Dc c := by
    intro c
    exact congrArg (fun F : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E => F c)
      (G.target_lower_right α β diag)
  have hmix : ‖(sumLeftProjection.comp ((G.targetOperator α β diag).comp sumRightInjection)).comp
      (Dc.symm : EuclideanSpace ℝ E →L[ℝ] EuclideanSpace ℝ E)‖ ≤ 3 := by
    dsimp only [Dc]
    rw [mediatorEquiv_symm_coe, target_upper_right, ← rectangularEuclideanCLM_square,
      ← rectangularEuclideanCLM_mul]
    exact (G.coupling_inverse_norm_le α β hα hβ hdeg).trans (by norm_num)
  exact mediator_residual_transfer (G.targetOperator α β diag) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection Dc _ α hα sumCoordinate_decomposition hDc
    sumLeftProjection_left sumRightProjection_left
    (G.target_operator_schur α β diag hα.ne' (coupling_ne_zero α β hα hβ))
    sumLeftProjection_norm_le sumRightProjection_norm_le hmix z g

end SignedIncidence

end Maxwell.Composition
