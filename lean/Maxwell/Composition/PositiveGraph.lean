import Maxwell.Composition.PositiveEdges

/-! The actual bipartite positive-unit graph, bounded degree and the fixed
finite diagonal alphabet inherited from the compiled circuit coefficients. -/
noncomputable section
namespace Maxwell.Composition.PositiveEdges
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveGraph (H : Matrix ι ι ℝ) :
    SignedIncidence ((ι ⊕ ι) ⊕ Edge H) (Edge H ⊕ Edge H) where
  tail e := Sum.inl (Sum.elim (fun e => Sum.inl e.val.1) (fun e => Sum.inr e.val.2) e)
  head e := Sum.inr (Sum.elim id id e)
  distinct _ := Sum.inl_ne_inr
  sign _ := 1
  abs_sign _ := abs_one

def diagonal (H : Matrix ι ι ℝ) : ((ι ⊕ ι) ⊕ Edge H) → ℝ :=
  Sum.elim (endpointDiagonal H) (fun e => -(weight H e)⁻¹)

theorem positive_degree_old (H : Matrix ι ι ℝ) (v : ι ⊕ ι) :
    (positiveGraph H).degree (Sum.inl v) = (graph H).degree v := by
  simp only [SignedIncidence.degree, Fintype.sum_sum_type]
  cases v with
  | inl i => simp [positiveGraph, graph]
  | inr j => simp [positiveGraph, graph]

theorem positive_degree_mediator (H : Matrix ι ι ℝ) (e : Edge H) :
    (positiveGraph H).degree (Sum.inr e) = 2 := by
  simp only [SignedIncidence.degree, Fintype.sum_sum_type]
  norm_num [positiveGraph]

theorem positive_degree_le_three (H : Matrix ι ι ℝ)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (v : (ι ⊕ ι) ⊕ Edge H) : (positiveGraph H).degree v ≤ 3 := by
  cases v with
  | inl v => rw [positive_degree_old]; exact degree_le_three H hr hc v
  | inr e => rw [positive_degree_mediator]; norm_num

omit [DecidableEq ι] in
theorem filter_eq_edge (H : Matrix ι ι ℝ) (e : Edge H) :
    Finset.filter (Eq e) Finset.univ = {e} := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact eq_comm

theorem matrix_eq_graph (H : Matrix ι ι ℝ) :
    matrix H = (positiveGraph H).logicalMatrix (diagonal H) := by
  ext i j
  simp only [SignedIncidence.logicalMatrix, Matrix.add_apply, SignedIncidence.adjacency, Fintype.sum_sum_type]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [matrix, positiveGraph, diagonal, Matrix.diagonal_apply]
    | inr j =>
      cases i <;>
        simp [matrix, positiveGraph, diagonal, SignedIncidence.incidence, graph, Finset.filter_and, eq_comm, filter_eq_edge, Finset.inter_singleton] <;> split_ifs <;> simp
  | inr i =>
    cases j with
    | inl j =>
      cases j <;>
        simp [matrix, positiveGraph, diagonal, SignedIncidence.incidence, graph, Finset.filter_and, eq_comm, filter_eq_edge, Finset.singleton_inter] <;> split_ifs <;> simp
    | inr j =>
      simp [matrix, diagonalMatrix, positiveGraph, diagonal, Matrix.diagonal_apply]

/-- The compiled gate alphabet includes zero entries of the dense matrix
representation, but no other nonzero coefficient. -/
def Alphabet (H : Matrix ι ι ℝ) : Prop := ∀ i j,
  H i j = 0 ∨ H i j = 1 ∨ H i j = -1 ∨ H i j = 1 / 2 ∨ H i j = -1 / 2

omit [Fintype ι] [DecidableEq ι] in
theorem alphabet_abs_le (H : Matrix ι ι ℝ) (h : Alphabet H) : ∀ i j, |H i j| ≤ 1 := by
  intro i j
  rcases h i j with h | h | h | h | h <;> rw [h] <;> norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem alphabet_half_integer (H : Matrix ι ι ℝ) (h : Alphabet H) (i j : ι) :
    ∃ a : ℤ, H i j = (a : ℝ) / 2 := by
  rcases h i j with h | h | h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨2, by norm_num; exact h⟩
  · exact ⟨-2, by norm_num; exact h⟩
  · exact ⟨1, by simpa using h⟩
  · exact ⟨-1, by simpa using h⟩

theorem endpoint_abs_le (H : Matrix ι ι ℝ) (habs : ∀ i j, |H i j| ≤ 1)
    (v : ι ⊕ ι) : |endpointDiagonal H v| ≤ (graph H).degree v := by
  rw [endpointDiagonal, abs_neg, ← (graph H).incidence_row_sum]
  calc
    |∑ e, (graph H).incidence v e * weight H e| ≤
        ∑ e, |(graph H).incidence v e * weight H e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, |(graph H).incidence v e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (habs e.val.1 e.val.2) (abs_nonneg _)).trans_eq (mul_one _)

theorem endpoint_half_integer (H : Matrix ι ι ℝ) (h : Alphabet H) (v : ι ⊕ ι) :
    ∃ a : ℤ, endpointDiagonal H v = (a : ℝ) / 2 := by
  choose a ha using alphabet_half_integer H h
  cases v with
  | inl i =>
    refine ⟨-∑ j, a i j, ?_⟩
    rw [endpointDiagonal_left]
    simp only [ha, Int.cast_neg, Int.cast_sum, Finset.sum_div, neg_div]
  | inr j =>
    refine ⟨-∑ i, a i j, ?_⟩
    rw [endpointDiagonal_right]
    simp only [ha, Int.cast_neg, Int.cast_sum, Finset.sum_div, neg_div]

theorem endpoint_alphabet (H : Matrix ι ι ℝ) (h : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) (v : ι ⊕ ι) :
    endpointDiagonal H v ∈ (Finset.Icc (-6 : ℤ) 6).image (fun a : ℤ => (a : ℝ) / 2) := by
  classical
  obtain ⟨a, ha⟩ := endpoint_half_integer H h v
  have hb := (endpoint_abs_le H (alphabet_abs_le H h) v).trans (degree_le_three H hr hc v)
  rw [ha, abs_le] at hb
  have hlo : (-6 : ℤ) ≤ a := by exact_mod_cast (show (-6 : ℝ) ≤ (a : ℝ) by linarith)
  have hhi : a ≤ (6 : ℤ) := by exact_mod_cast (show (a : ℝ) ≤ 6 by linarith)
  exact Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, ha.symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem mediator_alphabet (H : Matrix ι ι ℝ) (h : Alphabet H) (e : Edge H) :
    -(weight H e)⁻¹ ∈ ({-2, -1, 1, 2} : Finset ℝ) := by
  classical
  rcases h e.val.1 e.val.2 with h | h | h | h | h
  · exact False.elim (e.property h)
  all_goals norm_num [weight, h]

theorem diagonal_abs_le_three (H : Matrix ι ι ℝ) (h : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (v : (ι ⊕ ι) ⊕ Edge H) : |diagonal H v| ≤ 3 := by
  cases v with
  | inl v => exact (endpoint_abs_le H (alphabet_abs_le H h) v).trans (degree_le_three H hr hc v)
  | inr e =>
    have hm := mediator_alphabet H h e
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm | hm <;> change |-(weight H e)⁻¹| ≤ 3 <;> rw [hm] <;> norm_num

/-- Each matrix off-diagonal is exactly zero or positive one. -/
theorem offdiagonal_zero_or_one (H : Matrix ι ι ℝ)
    (i j : (ι ⊕ ι) ⊕ Edge H) (hij : i ≠ j) : matrix H i j = 0 ∨ matrix H i j = 1 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      left
      have h : i ≠ j := fun he => hij (congrArg Sum.inl he)
      simp [matrix, h]
    | inr e =>
      cases i with
      | inl i => simp only [matrix, Matrix.fromBlocks_apply₁₂, incidence_left]; split_ifs <;> simp
      | inr i => simp only [matrix, Matrix.fromBlocks_apply₁₂, incidence_right]; split_ifs <;> simp
  | inr e =>
    cases j with
    | inl j =>
      cases j with
      | inl j => simp only [matrix, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, incidence_left]; split_ifs <;> simp
      | inr j => simp only [matrix, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply, incidence_right]; split_ifs <;> simp
    | inr f =>
      left
      have h : e ≠ f := fun he => hij (congrArg Sum.inr he)
      simp [matrix, diagonalMatrix, h]

omit [DecidableEq ι] in
theorem edge_card_le (H : Matrix ι ι ℝ) (hr : ∀ i, (rowSupport H i).card ≤ 3) :
    Fintype.card (Edge H) ≤ 3 * Fintype.card ι := by
  classical
  have hs := sum_edges H (fun i j => if H i j ≠ 0 then (1 : ℝ) else 0)
    (by intros; simp_all)
  have hp (e : Edge H) : (if H e.val.1 e.val.2 ≠ 0 then (1 : ℝ) else 0) = 1 :=
    ite_eq_left e.property
  simp only [hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  simp_rw [Finset.sum_boole] at hs
  have hcard : (Fintype.card (Edge H) : ℝ) ≤ 3 * (Fintype.card ι : ℝ) := by
    calc
      _ = ∑ i, ((rowSupport H i).card : ℝ) := hs
      _ ≤ ∑ _i : ι, (3 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast hr i
      _ = _ := by simp; ring
  exact_mod_cast hcard

omit [DecidableEq ι] in
theorem vertex_card_le (H : Matrix ι ι ℝ) (hr : ∀ i, (rowSupport H i).card ≤ 3) :
    Fintype.card ((ι ⊕ ι) ⊕ Edge H) ≤ 5 * Fintype.card ι := by
  have he := edge_card_le H hr
  simp only [Fintype.card_sum]
  omega

end Maxwell.Composition.PositiveEdges
