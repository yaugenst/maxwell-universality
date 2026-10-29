import Maxwell.Composition.SubdivisionBlocks
import Maxwell.Composition.SubdivisionOperator
import Maxwell.Logical.PathOrder
import Maxwell.Logical.Routing.Subdivision

/-! Exact Schur elimination of the actual chronological routed edge paths.
The internal coordinates are precisely the subdivision vertices supplied by
the constructive lattice embedding, with one independent path per edge. -/

noncomputable section

namespace Maxwell.Composition.SubdivisionSchur

open Matrix
open Maxwell.Logical
open Maxwell.Logical.Routing
open scoped BigOperators

variable {V E : Type*}
variable {half : ℕ} (data : Gluing.Data V E half)

abbrev Internal := Σ e : E, Fin ((EdgeWalk.edgeWalk data e).length - 1)

def wireIndex (e : E) : ℕ :=
  ((EdgeWalk.edgeWalk data e).length - 1) / 4

theorem wireIndex_pos (e : E) : 0 < wireIndex data e := by
  obtain ⟨j, hj, he⟩ := Subdivision.internal_count_positive_wire_form data e
  simpa [wireIndex, he] using hj

theorem wireIndex_count (e : E) :
    (EdgeWalk.edgeWalk data e).length - 1 = 4 * wireIndex data e := by
  obtain ⟨j, _, he⟩ := Subdivision.internal_count_positive_wire_form data e
  simp [wireIndex, he]

def wireOrder (e : E) :
    Fin ((EdgeWalk.edgeWalk data e).length - 1) ≃ Fin (4 * wireIndex data e) :=
  finCongr (wireIndex_count data e)

def pathMatrix (e : E) : Matrix (Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (Fin ((EdgeWalk.edgeWalk data e).length - 1)) ℝ :=
  (PathOrder.adjacency (wireIndex data e)).submatrix (wireOrder data e) (wireOrder data e)

def pathInverse (e : E) : Matrix (Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (Fin ((EdgeWalk.edgeWalk data e).length - 1)) ℝ :=
  (PathOrder.inverse (wireIndex data e)).submatrix (wireOrder data e) (wireOrder data e)

def first (e : E) : Fin ((EdgeWalk.edgeWalk data e).length - 1) :=
  (wireOrder data e).symm (PathOrder.first (wireIndex data e) (wireIndex_pos data e))

def last (e : E) : Fin ((EdgeWalk.edgeWalk data e).length - 1) :=
  (wireOrder data e).symm (PathOrder.last (wireIndex data e) (wireIndex_pos data e))

@[simp] theorem first_val (e : E) : (first data e).val = 0 := rfl

@[simp] theorem last_val (e : E) :
    (last data e).val = (EdgeWalk.edgeWalk data e).length - 2 := by
  change 4 * wireIndex data e - 1 = _
  have h := wireIndex_count data e
  omega

theorem first_ne_last (e : E) : first data e ≠ last data e := by
  intro he
  have hv := congrArg Fin.val he
  rw [first_val, last_val] at hv
  have h := wireIndex_count data e
  have hp := wireIndex_pos data e
  omega

theorem pathMatrix_consecutive (e : E)
    (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    pathMatrix data e i j = if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  exact PathOrder.adjacency_eq_consecutive (wireIndex data e) (wireOrder data e i) (wireOrder data e j)

theorem pathMatrix_mul_inverse (e : E) : pathMatrix data e * pathInverse data e = 1 := by
  rw [pathMatrix, pathInverse, Matrix.submatrix_mul_equiv,
    PathOrder.adjacency_mul_inverse, Matrix.submatrix_one_equiv]

theorem pathInverse_mul_matrix (e : E) : pathInverse data e * pathMatrix data e = 1 := by
  exact mul_eq_one_comm.mpr (pathMatrix_mul_inverse data e)

@[simp] theorem pathInverse_first_first (e : E) : pathInverse data e (first data e) (first data e) = 0 := by
  simp [pathInverse, first]

@[simp] theorem pathInverse_last_last (e : E) : pathInverse data e (last data e) (last data e) = 0 := by
  simp [pathInverse, last]

@[simp] theorem pathInverse_first_last (e : E) : pathInverse data e (first data e) (last data e) = -1 := by
  simp [pathInverse, first, last]

@[simp] theorem pathInverse_last_first (e : E) : pathInverse data e (last data e) (first data e) = -1 := by
  simp [pathInverse, first, last]

theorem pathInverse_row_sum_le (e : E) (i : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    ∑ j, |pathInverse data e i j| ≤ ((EdgeWalk.edgeWalk data e).length - 1 : ℕ) := by
  unfold pathInverse
  simp only [Matrix.submatrix_apply]
  rw [(wireOrder data e).sum_comp (fun j : Fin (4 * wireIndex data e) =>
    |PathOrder.inverse (wireIndex data e) (wireOrder data e i) j|)]
  have h := PathOrder.inverse_row_abs_sum_le (wireIndex data e) (wireOrder data e i)
  have hcount : (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) =
      4 * (wireIndex data e : ℝ) := by exact_mod_cast wireIndex_count data e
  nlinarith [show 0 ≤ (wireIndex data e : ℝ) by positivity]

theorem pathInverse_col_sum_le (e : E) (j : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    ∑ i, |pathInverse data e i j| ≤ ((EdgeWalk.edgeWalk data e).length - 1 : ℕ) := by
  unfold pathInverse
  simp only [Matrix.submatrix_apply]
  rw [(wireOrder data e).sum_comp (fun i : Fin (4 * wireIndex data e) =>
    |PathOrder.inverse (wireIndex data e) i (wireOrder data e j)|)]
  have h := PathOrder.inverse_col_abs_sum_le (wireIndex data e) (wireOrder data e j)
  have hcount : (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) =
      4 * (wireIndex data e : ℝ) := by exact_mod_cast wireIndex_count data e
  nlinarith [show 0 ≤ (wireIndex data e : ℝ) by positivity]

variable [DecidableEq E]

def internalMatrix : Matrix (Internal data) (Internal data) ℝ :=
  Matrix.blockDiagonal' (pathMatrix data)

def internalInverse : Matrix (Internal data) (Internal data) ℝ :=
  Matrix.blockDiagonal' (pathInverse data)

variable [Fintype E]

theorem internalMatrix_mul_inverse : internalMatrix data * internalInverse data = 1 := by
  rw [internalMatrix, internalInverse, ← Matrix.blockDiagonal'_mul]
  simp only [pathMatrix_mul_inverse]
  exact Matrix.blockDiagonal'_one

theorem internalInverse_mul_matrix : internalInverse data * internalMatrix data = 1 := by
  exact mul_eq_one_comm.mpr (internalMatrix_mul_inverse data)

def internalEquiv : EuclideanSpace ℝ (Internal data) ≃L[ℝ] EuclideanSpace ℝ (Internal data) :=
  ContinuousLinearEquiv.equivOfInverse'
    (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalMatrix data))
    (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalInverse data))
    (by
      change (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalMatrix data)) *
        (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalInverse data)) = 1
      rw [← map_mul, internalMatrix_mul_inverse, map_one])
    (by
      change (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalInverse data)) *
        (Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalMatrix data)) = 1
      rw [← map_mul, internalInverse_mul_matrix, map_one])

@[simp] theorem internalEquiv_coe :
    (internalEquiv data : EuclideanSpace ℝ (Internal data) →L[ℝ] EuclideanSpace ℝ (Internal data)) =
      Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalMatrix data) := rfl

@[simp] theorem internalEquiv_symm_coe :
    ((internalEquiv data).symm : EuclideanSpace ℝ (Internal data) →L[ℝ] EuclideanSpace ℝ (Internal data)) =
      Matrix.toEuclideanCLM (n := Internal data) (𝕜 := ℝ) (internalInverse data) := rfl

theorem internal_inverse_norm_le (ell : ℝ) (hell : 0 ≤ ell)
    (hlength : ∀ e, (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) ≤ ell) :
    ‖((internalEquiv data).symm : EuclideanSpace ℝ (Internal data) →L[ℝ]
      EuclideanSpace ℝ (Internal data))‖ ≤ ell := by
  apply SubdivisionBlocks.blockDiagonal_norm_le (pathInverse data) ell hell
  · intro e i
    exact (pathInverse_row_sum_le data e i).trans (hlength e)
  · intro e j
    exact (pathInverse_col_sum_le data e j).trans (hlength e)

variable [DecidableEq V]

def coupling (G : SignedIncidence V E) : Matrix V (Internal data) ℝ :=
  SubdivisionBlocks.coupling G (first data) (last data)

def matrix (G : SignedIncidence V E) (diagonal : V → ℝ) :
    Matrix (Subdivision.Vertex data) (Subdivision.Vertex data) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal diagonal) (coupling data G)
    (coupling data G).transpose (internalMatrix data)

/-- Eliminating every actual internal path gives precisely the original
signed graph, with its original terminal diagonal unchanged. -/
theorem schur (G : SignedIncidence V E) (diagonal : V → ℝ) :
    Matrix.diagonal diagonal - coupling data G * internalInverse data * (coupling data G).transpose =
      G.logicalMatrix diagonal := by
  rw [coupling, internalInverse,
    SubdivisionBlocks.schur_correction G (first data) (last data) (pathInverse data)
      (pathInverse_first_first data) (pathInverse_last_last data)
      (pathInverse_first_last data) (pathInverse_last_first data)]
  simp only [sub_neg_eq_add, SignedIncidence.logicalMatrix]

variable [Fintype V]

theorem coupling_norm_le_two (G : SignedIncidence V E) (hdegree : ∀ v, G.degree v ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (coupling data G)‖ ≤ 2 :=
  SubdivisionBlocks.coupling_norm_le_two G (first data) (last data) (first_ne_last data) hdegree

theorem coupling_transpose_norm_le_two (G : SignedIncidence V E) (hdegree : ∀ v, G.degree v ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (coupling data G).transpose‖ ≤ 2 := by
  have h := Maxwell.rectangularEuclideanCLM_norm_le_sqrt (coupling data G).transpose 1 3
    (by norm_num) (by norm_num)
    (SubdivisionBlocks.coupling_col_abs_sum_le G (first data) (last data) (first_ne_last data))
    (fun v => (SubdivisionBlocks.coupling_row_abs_sum_le G (first data) (last data) v).trans (hdegree v))
  refine h.trans ?_
  norm_num only [one_mul]
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

def operator (G : SignedIncidence V E) (diagonal : V → ℝ) :
    EuclideanSpace ℝ (Subdivision.Vertex data) →L[ℝ] EuclideanSpace ℝ (Subdivision.Vertex data) :=
  SubdivisionOperator.operator (Matrix.diagonal diagonal) (coupling data G) (internalMatrix data)

def source (g : EuclideanSpace ℝ V) : EuclideanSpace ℝ (Subdivision.Vertex data) :=
  sumLeftInjection (κ := Internal data) g

/-- The full routed inverse is constructed using the explicit inverses of
the actual internal paths and an inverse of the original terminal graph. -/
def equiv (G : SignedIncidence V E) (diagonal : V → ℝ)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diagonal)) :
    EuclideanSpace ℝ (Subdivision.Vertex data) ≃L[ℝ] EuclideanSpace ℝ (Subdivision.Vertex data) :=
  SubdivisionOperator.equiv (Matrix.diagonal diagonal) (coupling data G)
    (internalMatrix data) (internalInverse data) (internalEquiv data) S
    (internalEquiv_coe data) (internalEquiv_symm_coe data)
    (by simpa only [SubdivisionOperator.schurMatrix, schur] using hS)

@[simp] theorem equiv_coe (G : SignedIncidence V E) (diagonal : V → ℝ)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diagonal)) :
    (equiv data G diagonal S hS : EuclideanSpace ℝ (Subdivision.Vertex data) →L[ℝ]
      EuclideanSpace ℝ (Subdivision.Vertex data)) = operator data G diagonal := rfl

theorem inverse_norm_le (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diagonal))
    (ell Q : ℝ) (hell : 0 ≤ ell)
    (hlength : ∀ e, (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) ≤ ell)
    (hSinv : ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Q) :
    ‖((equiv data G diagonal S hS).symm : EuclideanSpace ℝ (Subdivision.Vertex data) →L[ℝ]
      EuclideanSpace ℝ (Subdivision.Vertex data))‖ ≤ (1 + 2 * ell) ^ 2 * Q + ell := by
  exact SubdivisionOperator.inverse_norm_le (Matrix.diagonal diagonal) (coupling data G)
    (internalMatrix data) (internalInverse data) (internalEquiv data) S
    (internalEquiv_coe data) (internalEquiv_symm_coe data)
    (by simpa only [SubdivisionOperator.schurMatrix, schur] using hS)
    ell Q hell (coupling_norm_le_two data G hdegree)
    (coupling_transpose_norm_le_two data G hdegree)
    (internal_inverse_norm_le data ell hell hlength) hSinv

theorem inverse_norm_le_polynomial (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (S : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hS : (S : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) =
      Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diagonal))
    (ell Q : ℝ) (hell : 1 ≤ ell)
    (hlength : ∀ e, (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) ≤ ell)
    (hSinv : ‖(S.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ Q) :
    ‖((equiv data G diagonal S hS).symm : EuclideanSpace ℝ (Subdivision.Vertex data) →L[ℝ]
      EuclideanSpace ℝ (Subdivision.Vertex data))‖ ≤ 9 * ell ^ 2 * (Q + ell) :=
  (inverse_norm_le data G diagonal hdegree S hS ell Q (by linarith) hlength hSinv).trans
    (SubdivisionOperator.polynomial_bound ell Q hell ((norm_nonneg _).trans hSinv))

/-- Arbitrary residuals on the internal subdivision vertices are retained
and transferred with a norm factor independent of the number of paths. -/
theorem residual_transfer (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hdegree : ∀ v, G.degree v ≤ 3) (ell : ℝ) (hell : 0 ≤ ell)
    (hlength : ∀ e, (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) ≤ ell)
    (z : EuclideanSpace ℝ (Subdivision.Vertex data)) (g : EuclideanSpace ℝ V) :
    ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diagonal)
        (sumLeftProjection (κ := Internal data) z) - g‖ ≤
      (1 + 2 * ell) * ‖operator data G diagonal z - source data g‖ := by
  have h := SubdivisionOperator.residual_transfer (Matrix.diagonal diagonal) (coupling data G)
    (internalMatrix data) (internalInverse data) (internalEquiv data)
    (internalEquiv_coe data) (internalEquiv_symm_coe data)
    ell (coupling_norm_le_two data G hdegree) (internal_inverse_norm_le data ell hell hlength) z g
  rw [SubdivisionOperator.schurMatrix, schur] at h
  convert h using 1
  rfl

omit [DecidableEq E] [Fintype E] [DecidableEq V] [Fintype V] in
theorem internal_length_bound (e : E) :
    (((EdgeWalk.edgeWalk data e).length - 1 : ℕ) : ℝ) ≤ 1024 * (2 * half : ℕ) := by
  have h := EdgeWalk.edgeWalk_length_bound data e
  exact_mod_cast (show (EdgeWalk.edgeWalk data e).length - 1 ≤ 1024 * (2 * half) by omega)

omit [Fintype V] [Fintype E] in
theorem matrix_terminal_internal (G : SignedIncidence V E) (diagonal : V → ℝ)
    (v : V) (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    matrix data G diagonal (Sum.inl v) (Sum.inr ⟨e, t⟩) =
      (if t = first data e ∧ v = G.tail e then 1 else 0) +
      (if t = last data e ∧ v = G.head e then G.sign e else 0) := rfl

omit [Fintype V] [Fintype E] in
theorem matrix_internal_same (G : SignedIncidence V E) (diagonal : V → ℝ)
    (e : E) (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    matrix data G diagonal (Sum.inr ⟨e, i⟩) (Sum.inr ⟨e, j⟩) =
      if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  simp only [matrix, Matrix.fromBlocks_apply₂₂, internalMatrix,
    Matrix.blockDiagonal'_apply_eq, pathMatrix_consecutive]

omit [Fintype V] [Fintype E] in
theorem matrix_internal_different (G : SignedIncidence V E) (diagonal : V → ℝ)
    (e f : E) (hef : e ≠ f) (i : Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (j : Fin ((EdgeWalk.edgeWalk data f).length - 1)) :
    matrix data G diagonal (Sum.inr ⟨e, i⟩) (Sum.inr ⟨f, j⟩) = 0 := by
  exact Matrix.blockDiagonal'_apply_ne (pathMatrix data) i j hef

omit [DecidableEq E] [DecidableEq V] in
@[simp] theorem original_coordinate
    (z : EuclideanSpace ℝ (Subdivision.Vertex data)) (v : V) :
    sumLeftProjection z v = z (Sum.inl v) := rfl

end Maxwell.Composition.SubdivisionSchur
