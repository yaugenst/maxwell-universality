import Maxwell.Interfaces
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact relative-PEC scalar Maxwell target

The finite target below uses every square face, deletes tangential boundary
electric edges, and orients the incidence by
`Curl_a = D_b E_c - D_c E_b`, with `(a,b,c)` cyclic.  Transverse coordinates
of retained edges are positive: the stored index `j` denotes vertex `j+1`.
All entries and scalar-cell averages are exact rationals.
-/

namespace Maxwell.Target

structure Box where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  deriving DecidableEq

abbrev Box.Edge (B : Box) := RetainedEdge B.nx B.ny B.nz
abbrev Box.Cell (B : Box) := Maxwell.Cell B.nx B.ny B.nz

/-- Faces normal to x, y, and z, in that order. Boundary faces are retained. -/
abbrev Box.Face (B : Box) :=
  (Fin (B.nx + 1) × Fin B.ny × Fin B.nz) ⊕
    ((Fin B.nx × Fin (B.ny + 1) × Fin B.nz) ⊕
      (Fin B.nx × Fin B.ny × Fin (B.nz + 1)))

/-- Positive interior vertex, in the full vertex coordinate type. -/
def interiorVertex {n : ℕ} (v : Fin (n - 1)) : Fin (n + 1) :=
  ⟨v.val + 1, by have := v.isLt; omega⟩

/-- The four faces incident to a retained edge, with signs `+,-,-,+`.
For example, an x-edge at `(i,j+1,k+1)` occurs positively on the lower
y-face and upper z-face, and negatively on the upper y-face and lower
z-face. This is exactly `Curl_y = D_z E_x - D_x E_z` and
`Curl_z = D_x E_y - D_y E_x`. The other edge orientations are cyclic. -/
def incidentFaces {B : Box} (e : B.Edge) : Fin 4 → B.Face :=
  match e with
  | .inl (i, j, k) =>
      ![.inr (.inl (i, interiorVertex j, interiorLower k)),
        .inr (.inl (i, interiorVertex j, interiorUpper k)),
        .inr (.inr (i, interiorLower j, interiorVertex k)),
        .inr (.inr (i, interiorUpper j, interiorVertex k))]
  | .inr (.inl (i, j, k)) =>
      ![.inr (.inr (interiorLower i, j, interiorVertex k)),
        .inr (.inr (interiorUpper i, j, interiorVertex k)),
        .inl (interiorVertex i, j, interiorLower k),
        .inl (interiorVertex i, j, interiorUpper k)]
  | .inr (.inr (i, j, k)) =>
      ![.inl (interiorVertex i, interiorLower j, k),
        .inl (interiorVertex i, interiorUpper j, k),
        .inr (.inl (interiorLower i, interiorVertex j, k)),
        .inr (.inl (interiorUpper i, interiorVertex j, k))]

theorem incidentFaces_injective {B : Box} (e : B.Edge) :
    Function.Injective (incidentFaces e) := by
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    intro a b h <;> fin_cases a <;> fin_cases b <;>
    simp [incidentFaces, Fin.ext_iff, interiorLower, interiorUpper] at h ⊢

def incidenceSign : Fin 4 → ℚ := ![1, -1, -1, 1]

theorem incidenceSign_ne_zero (a : Fin 4) : incidenceSign a ≠ 0 := by
  fin_cases a <;> norm_num [incidenceSign]

theorem incidenceSign_sq (a : Fin 4) : incidenceSign a * incidenceSign a = 1 := by
  fin_cases a <;> norm_num [incidenceSign]

theorem incidenceSign_abs (a : Fin 4) : |incidenceSign a| = 1 := by
  fin_cases a <;> norm_num [incidenceSign]

/-- Exact oriented face-edge incidence; absent PEC boundary edges contribute
zero because they have no inhabitant in `Box.Edge`. -/
def curl (B : Box) : Matrix B.Face B.Edge ℚ := fun f e =>
  ∑ a : Fin 4, if f = incidentFaces e a then incidenceSign a else 0

theorem curl_incident {B : Box} (e : B.Edge) (a : Fin 4) :
    curl B (incidentFaces e a) e = incidenceSign a := by
  have h : ∀ b, incidentFaces e a = incidentFaces e b ↔ a = b :=
    fun b => (incidentFaces_injective e).eq_iff
  simp [curl, h]

theorem curl_not_incident {B : Box} (e : B.Edge) (f : B.Face)
    (h : ∀ a, f ≠ incidentFaces e a) : curl B f e = 0 := by
  simp [curl, h]

theorem curl_ne_zero_iff {B : Box} (e : B.Edge) (f : B.Face) :
    curl B f e ≠ 0 ↔ ∃ a, f = incidentFaces e a := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact h (curl_not_incident e f hn)
  · rintro ⟨a, rfl⟩
    rw [curl_incident]
    exact incidenceSign_ne_zero a

/-- Every retained edge has exactly four nonzero face incidences, even when
one or more of these faces lies next to the PEC boundary. -/
theorem curl_column_nnz {B : Box} (e : B.Edge) :
    (Finset.univ.filter (fun f : B.Face => curl B f e ≠ 0)).card = 4 := by
  have hs : Finset.univ.filter (fun f : B.Face => curl B f e ≠ 0) =
      Finset.univ.image (incidentFaces e) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, curl_ne_zero_iff,
      Finset.mem_image]
    constructor
    · rintro ⟨a, h⟩
      exact ⟨a, h.symm⟩
    · rintro ⟨a, h⟩
      exact ⟨a, h.symm⟩
  rw [hs, Finset.card_image_of_injective _ (incidentFaces_injective e)]
  simp

theorem curl_entry_sq {B : Box} (e : B.Edge) (f : B.Face) :
    curl B f e * curl B f e =
      ∑ a : Fin 4, if f = incidentFaces e a then (1 : ℚ) else 0 := by
  by_cases h : ∃ a, f = incidentFaces e a
  · rcases h with ⟨a, rfl⟩
    have hi : ∀ b, incidentFaces e a = incidentFaces e b ↔ a = b :=
      fun b => (incidentFaces_injective e).eq_iff
    simp [curl_incident, incidenceSign_sq, hi]
  · push Not at h
    simp [curl_not_incident e f h, h]

/-- Size-independent exact diagonal of the curl Gram matrix. -/
theorem curl_gram_diagonal {B : Box} (e : B.Edge) :
    ((curl B).transpose * curl B) e e = 4 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, curl_entry_sq]
  rw [Finset.sum_comm]
  simp

theorem curl_abs_eq_sq {B : Box} (f : B.Face) (e : B.Edge) :
    |curl B f e| = curl B f e * curl B f e := by
  by_cases h : ∃ a, f = incidentFaces e a
  · rcases h with ⟨a, rfl⟩
    rw [curl_incident, incidenceSign_abs, incidenceSign_sq]
  · push Not at h
    rw [curl_not_incident e f h]
    norm_num

/-- The column absolute sum is exactly four, uniformly over all box sizes. -/
theorem curl_column_abs_sum {B : Box} (e : B.Edge) :
    ∑ f : B.Face, |curl B f e| = 4 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← curl_abs_eq_sq] using
    curl_gram_diagonal e

/-- Raw scalar-cell Maxwell operator, at the fixed squared frequency `1/64`.
The raw form is useful for stating shifts independently of interval bounds. -/
def operator (B : Box) (material : B.Cell → ℚ) : Matrix B.Edge B.Edge ℚ :=
  (curl B).transpose * curl B - (1 / 64 : ℚ) • Matrix.diagonal (edgeAverage material)

/-- Admissible target: one rational scalar in `[1,25]` per physical cell. -/
def maxwell {B : Box} (material : ScalarMaterial B.nx B.ny B.nz) :
    Matrix B.Edge B.Edge ℚ := operator B material.value

theorem operator_symmetric (B : Box) (material : B.Cell → ℚ) :
    (operator B material).IsSymm := by
  unfold Matrix.IsSymm operator
  simp [Matrix.transpose_sub, Matrix.transpose_mul]

theorem maxwell_symmetric {B : Box} (material : ScalarMaterial B.nx B.ny B.nz) :
    (maxwell material).IsSymm := operator_symmetric B material.value

/-- Shifting every scalar cell by `64*u` shifts the complete Maxwell matrix
by `-u I`, including its curl part and all off-diagonal entries. -/
theorem operator_uniform_shift (B : Box) (material : B.Cell → ℚ) (u : ℚ) :
    operator B (fun c => material c + 64 * u) =
      operator B material - u • (1 : Matrix B.Edge B.Edge ℚ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [operator, Matrix.sub_apply, Matrix.smul_apply, edgeAverage_uniform_shift]
    ring
  · simp [operator, Matrix.sub_apply, Matrix.smul_apply, h]

theorem operator_diagonal (B : Box) (material : B.Cell → ℚ) (e : B.Edge) :
    operator B material e e = 4 - (1 / 64 : ℚ) * edgeAverage material e := by
  simp [operator, curl_gram_diagonal]

/-- The admissible scalar mass does not reverse the sign of a diagonal
entry: the exact full diagonal remains in `[231/64,255/64]`. -/
theorem maxwell_diagonal_bounds {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (e : B.Edge) :
    231 / 64 ≤ maxwell material e e ∧ maxwell material e e ≤ 255 / 64 := by
  have hb := edgeAverage_bounds material e
  change 231 / 64 ≤ operator B material.value e e ∧
    operator B material.value e e ≤ 255 / 64
  rw [operator_diagonal]
  constructor <;> linarith

theorem maxwell_diagonal_nonneg {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (e : B.Edge) :
    0 ≤ maxwell material e e := by
  have h := (maxwell_diagonal_bounds material e).1
  linarith

/-- Entrywise, subtracting the admissible scalar mass can only decrease
the absolute values: the positive diagonal remains positive and the
off-diagonal entries are unchanged. -/
theorem maxwell_abs_le_gram {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (e e' : B.Edge) :
    |maxwell material e e'| ≤ |((curl B).transpose * curl B) e e'| := by
  by_cases h : e = e'
  · subst e'
    rw [abs_of_nonneg (maxwell_diagonal_nonneg material e), curl_gram_diagonal]
    norm_num
    have hm := (maxwell_diagonal_bounds material e).2
    linarith
  · simp [maxwell, operator, Matrix.sub_apply, Matrix.smul_apply, h]

/-- The one-edge box with constant material one has the claimed exact
Maxwell scalar `255/64`. -/
theorem one_edge_operator (e : (Box.mk 1 2 2).Edge) :
    operator (Box.mk 1 2 2) (fun _ => 1) e e = 255 / 64 := by
  rw [operator_diagonal, edgeAverage_constant]
  norm_num

end Maxwell.Target
