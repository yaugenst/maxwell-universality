import Maxwell.Composition.SignedMediator

/-! The positive-unit graph is computed from the actual nonzero entries of
H. Its vertices, edges, coefficients and diagonal corrections are definitions,
not an assumed graph representation. -/
noncomputable section
namespace Maxwell.Composition.PositiveEdges
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Edge (H : Matrix ι ι ℝ) := {p : ι × ι // H p.1 p.2 ≠ 0}
instance edgeFinite (H : Matrix ι ι ℝ) : Finite (Edge H) := inferInstanceAs (Finite {p : ι × ι // H p.1 p.2 ≠ 0})
noncomputable instance edgeFintype (H : Matrix ι ι ℝ) : Fintype (Edge H) := Fintype.ofFinite _
noncomputable instance edgeDecidableEq (H : Matrix ι ι ℝ) : DecidableEq (Edge H) := Classical.decEq _

def weight (H : Matrix ι ι ℝ) (e : Edge H) : ℝ := H e.val.1 e.val.2

def graph (H : Matrix ι ι ℝ) : SignedIncidence (ι ⊕ ι) (Edge H) where
  tail e := Sum.inl e.val.1
  head e := Sum.inr e.val.2
  distinct _ := Sum.inl_ne_inr
  sign _ := 1
  abs_sign _ := abs_one

def symmetricMatrix (H : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 H H.transpose 0

def endpointDiagonal (H : Matrix ι ι ℝ) (v : ι ⊕ ι) : ℝ :=
  -∑ e : Edge H, (graph H).incidence v e * weight H e

def diagonalMatrix (H : Matrix ι ι ℝ) : Matrix (Edge H) (Edge H) ℝ :=
  Matrix.diagonal fun e => -(weight H e)⁻¹

def diagonalInverse (H : Matrix ι ι ℝ) : Matrix (Edge H) (Edge H) ℝ :=
  Matrix.diagonal fun e => -weight H e

def matrix (H : Matrix ι ι ℝ) : Matrix ((ι ⊕ ι) ⊕ Edge H) ((ι ⊕ ι) ⊕ Edge H) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal (endpointDiagonal H)) (graph H).incidence
    (graph H).incidence.transpose (diagonalMatrix H)

omit [Fintype ι] in
@[simp] theorem incidence_left (H : Matrix ι ι ℝ) (i : ι) (e : Edge H) :
    (graph H).incidence (Sum.inl i) e = if i = e.val.1 then 1 else 0 := by
  simp [graph, SignedIncidence.incidence]

omit [Fintype ι] in
@[simp] theorem incidence_right (H : Matrix ι ι ℝ) (i : ι) (e : Edge H) :
    (graph H).incidence (Sum.inr i) e = if i = e.val.2 then 1 else 0 := by
  simp [graph, SignedIncidence.incidence]

omit [DecidableEq ι] in
theorem sum_edges (H : Matrix ι ι ℝ) (f : ι → ι → ℝ)
    (hf : ∀ i j, H i j = 0 → f i j = 0) :
    ∑ e : Edge H, f e.val.1 e.val.2 = ∑ i, ∑ j, f i j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : ι × ι => H p.1 p.2 ≠ 0)
    (fun p => f p.1 p.2)
  have hz : (∑ p : {p : ι × ι // ¬ H p.1 p.2 ≠ 0}, f p.val.1 p.val.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact hf p.val.1 p.val.2 (not_not.mp p.property)
  rw [hz, add_zero, Fintype.sum_prod_type] at h
  convert h using 1; congr 1
  exact congrArg (fun ft : Fintype (Edge H) => @Fintype.elems (Edge H) ft) (Subsingleton.elim _ _)

theorem endpointDiagonal_left (H : Matrix ι ι ℝ) (i : ι) :
    endpointDiagonal H (Sum.inl i) = -∑ j, H i j := by
  classical
  rw [endpointDiagonal]
  simp only [incidence_left, weight, ite_mul, one_mul, zero_mul]
  rw [sum_edges H (fun a b => if i = a then H a b else 0)
    (by intros; simp_all)]
  simp

theorem endpointDiagonal_right (H : Matrix ι ι ℝ) (i : ι) :
    endpointDiagonal H (Sum.inr i) = -∑ j, H j i := by
  classical
  rw [endpointDiagonal]
  simp only [incidence_right, weight, ite_mul, one_mul, zero_mul]
  rw [sum_edges H (fun a b => if i = b then H a b else 0)
    (by intros; simp_all)]
  simp

/-- The exact positive-unit mediator Schur complement, with one mediator for
 each actual nonzero coefficient of H. -/
theorem schur (H : Matrix ι ι ℝ) :
    Matrix.diagonal (endpointDiagonal H) -
      (graph H).incidence * diagonalInverse H * (graph H).incidence.transpose =
      symmetricMatrix H := by
  classical
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp only [diagonalInverse, Matrix.mul_diagonal, Matrix.transpose_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [incidence_left, weight]
      rw [sum_edges H (fun a b => (if i = a then 1 else 0) * -H a b *
        (if j = a then 1 else 0)) (by intros; simp_all)]
      by_cases hij : i = j
      · subst j
        simp [endpointDiagonal_left, symmetricMatrix]
      · simp [hij, symmetricMatrix, mul_ite, ite_mul]
    | inr j =>
      simp only [incidence_left, incidence_right, weight]
      rw [sum_edges H (fun a b => (if i = a then 1 else 0) * -H a b *
        (if j = b then 1 else 0)) (by intros; simp_all)]
      simp [symmetricMatrix, mul_ite, ite_mul]
  | inr i =>
    cases j with
    | inl j =>
      simp only [incidence_left, incidence_right, weight]
      rw [sum_edges H (fun a b => (if i = b then 1 else 0) * -H a b *
        (if j = a then 1 else 0)) (by intros; simp_all)]
      simp [symmetricMatrix, mul_ite, ite_mul]
    | inr j =>
      simp only [incidence_right, weight]
      rw [sum_edges H (fun a b => (if i = b then 1 else 0) * -H a b *
        (if j = b then 1 else 0)) (by intros; simp_all)]
      by_cases hij : i = j
      · subst j
        simp [endpointDiagonal_right, symmetricMatrix]
      · simp [hij, symmetricMatrix, mul_ite, ite_mul]

omit [DecidableEq ι] in
theorem diagonal_mul_inverse (H : Matrix ι ι ℝ) :
    diagonalMatrix H * diagonalInverse H = 1 := by
  rw [diagonalMatrix, diagonalInverse, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [weight, i.property]
  · simp [h]

omit [DecidableEq ι] in
theorem inverse_mul_diagonal (H : Matrix ι ι ℝ) :
    diagonalInverse H * diagonalMatrix H = 1 := by
  rw [diagonalMatrix, diagonalInverse, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [weight, i.property]
  · simp [h]

def rowSupport (H : Matrix ι ι ℝ) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun j => H i j ≠ 0

def columnSupport (H : Matrix ι ι ℝ) (j : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => H i j ≠ 0

theorem degree_left (H : Matrix ι ι ℝ) (i : ι) :
    (graph H).degree (Sum.inl i) = (rowSupport H i).card := by
  classical
  simp only [SignedIncidence.degree, graph, Sum.inl.injEq, Sum.inl_ne_inr, or_false]
  have hs : (∑ e : Edge H, if i = e.val.1 then (1 : ℝ) else 0) =
      ∑ e : Edge H, if H e.val.1 e.val.2 ≠ 0 then
        (if i = e.val.1 then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [ite_eq_left e.property]
  rw [hs, sum_edges H (fun a b => if H a b ≠ 0 then (if i = a then 1 else 0) else 0)
    (by intros; simp_all)]
  have hp (a b : ι) : (if H a b ≠ 0 then (if i = a then (1 : ℝ) else 0) else 0) =
      if i = a then (if H a b ≠ 0 then 1 else 0) else 0 := by split_ifs <;> rfl
  simp_rw [hp]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]
  simp only [rowSupport, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem degree_right (H : Matrix ι ι ℝ) (j : ι) :
    (graph H).degree (Sum.inr j) = (columnSupport H j).card := by
  classical
  simp only [SignedIncidence.degree, graph, Sum.inr.injEq, Sum.inr_ne_inl, false_or]
  have hs : (∑ e : Edge H, if j = e.val.2 then (1 : ℝ) else 0) =
      ∑ e : Edge H, if H e.val.1 e.val.2 ≠ 0 then
        (if j = e.val.2 then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [ite_eq_left e.property]
  rw [hs, sum_edges H (fun a b => if H a b ≠ 0 then (if j = b then 1 else 0) else 0)
    (by intros; simp_all)]
  have hp (a b : ι) : (if H a b ≠ 0 then (if j = b then (1 : ℝ) else 0) else 0) =
      if j = b then (if H a b ≠ 0 then 1 else 0) else 0 := by split_ifs <;> rfl
  simp_rw [hp]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left]
  simp only [columnSupport, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem degree_le_three (H : Matrix ι ι ℝ)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) (v : ι ⊕ ι) :
    (graph H).degree v ≤ 3 := by
  cases v with
  | inl i => rw [degree_left]; exact_mod_cast hr i
  | inr j => rw [degree_right]; exact_mod_cast hc j

theorem incidence_norm_le (H : Matrix ι ι ℝ)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (graph H).incidence‖ ≤ Real.sqrt 6 := by
  have h := Maxwell.rectangularEuclideanCLM_norm_le_sqrt (graph H).incidence 3 2
    (by norm_num) (by norm_num)
    (fun v => by rw [(graph H).incidence_row_sum]; exact degree_le_three H hr hc v)
    (fun e => ((graph H).incidence_column_sum e).le)
  norm_num at h ⊢
  exact h

end Maxwell.Composition.PositiveEdges
