import Maxwell.Composition.SubdivisionSchur

/-! The nonzero off-diagonal entries of the assembled subdivision matrix
are genuine nearest-neighbor edges of its constructed lattice embedding. -/

noncomputable section

namespace Maxwell.Composition.SubdivisionSchur

open Maxwell.Logical.Routing

variable {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)

theorem first_adjacent (e : E) :
    UnitAdjacent (Subdivision.embedding data (Sum.inl (data.endpoint e false)))
      (Subdivision.embedding data (Sum.inr ⟨e, first data e⟩)) := by
  change UnitAdjacent (Gluing.vertexPoint data (data.endpoint e false))
    ((EdgeWalk.edgeWalk data e).point ((first data e).val + 1))
  rw [first_val]
  simpa only [(EdgeWalk.edgeWalk data e).first] using
    (EdgeWalk.edgeWalk data e).step 0 (by have h := (first data e).isLt; omega)

theorem last_adjacent (e : E) :
    UnitAdjacent (Subdivision.embedding data (Sum.inl (data.endpoint e true)))
      (Subdivision.embedding data (Sum.inr ⟨e, last data e⟩)) := by
  change UnitAdjacent (Gluing.vertexPoint data (data.endpoint e true))
    ((EdgeWalk.edgeWalk data e).point ((last data e).val + 1))
  have hp := (last data e).isLt
  rw [last_val] at hp ⊢
  apply (Walk.unitAdjacent_symm _ _).mpr
  have he : (EdgeWalk.edgeWalk data e).length - 2 + 1 + 1 =
      (EdgeWalk.edgeWalk data e).length := by omega
  simpa only [he, (EdgeWalk.edgeWalk data e).last] using (EdgeWalk.edgeWalk data e).step
    ((EdgeWalk.edgeWalk data e).length - 2 + 1) (by omega)

theorem internal_adjacent (e : E)
    (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    UnitAdjacent (Subdivision.embedding data (Sum.inr ⟨e, i⟩))
      (Subdivision.embedding data (Sum.inr ⟨e, j⟩)) := by
  change UnitAdjacent ((EdgeWalk.edgeWalk data e).point (i.val + 1))
    ((EdgeWalk.edgeWalk data e).point (j.val + 1))
  rcases hij with hij | hji
  · rw [← hij]
    exact (EdgeWalk.edgeWalk data e).step _ (by have hi := i.isLt; omega)
  · apply (Walk.unitAdjacent_symm _ _).mpr
    rw [← hji]
    exact (EdgeWalk.edgeWalk data e).step _ (by have hj := j.isLt; omega)

variable [DecidableEq V] [DecidableEq E]

theorem terminal_internal_adjacent (G : SignedIncidence V E) (diagonal : V → ℝ)
    (htail : ∀ e, G.tail e = data.endpoint e false)
    (hhead : ∀ e, G.head e = data.endpoint e true)
    (v : V) (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (hnz : matrix data G diagonal (Sum.inl v) (Sum.inr ⟨e, t⟩) ≠ 0) :
    UnitAdjacent (Subdivision.embedding data (Sum.inl v))
      (Subdivision.embedding data (Sum.inr ⟨e, t⟩)) := by
  rw [matrix_terminal_internal] at hnz
  by_cases hfirst : t = first data e ∧ v = G.tail e
  · rcases hfirst with ⟨rfl, rfl⟩
    rw [htail]
    exact first_adjacent data e
  · by_cases hlast : t = last data e ∧ v = G.head e
    · rcases hlast with ⟨rfl, rfl⟩
      rw [hhead]
      exact last_adjacent data e
    · simp only [hfirst, hlast, ↓reduceIte, add_zero] at hnz
      exact (hnz rfl).elim

/-- Every actual off-diagonal matrix nonzero lies on an actual unit edge;
no separate support or geometric realizability premise is imposed. -/
theorem matrix_local (G : SignedIncidence V E) (diagonal : V → ℝ)
    (htail : ∀ e, G.tail e = data.endpoint e false)
    (hhead : ∀ e, G.head e = data.endpoint e true)
    (a b : Subdivision.Vertex data) (hab : a ≠ b)
    (hnz : matrix data G diagonal a b ≠ 0) :
    UnitAdjacent (Subdivision.embedding data a) (Subdivision.embedding data b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hab' : a ≠ b := fun h => hab (congrArg Sum.inl h)
      simp only [matrix, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_ne _ hab'] at hnz
      exact (hnz rfl).elim
    | inr b =>
      rcases b with ⟨e, t⟩
      exact terminal_internal_adjacent data G diagonal htail hhead a e t hnz
  | inr a =>
    rcases a with ⟨e, t⟩
    cases b with
    | inl b =>
      apply (Walk.unitAdjacent_symm _ _).mpr
      exact terminal_internal_adjacent data G diagonal htail hhead b e t hnz
    | inr b =>
      rcases b with ⟨f, u⟩
      by_cases hef : e = f
      · subst f
        rw [matrix_internal_same] at hnz
        by_cases hstep : t.val + 1 = u.val ∨ u.val + 1 = t.val
        · exact internal_adjacent data e t u hstep
        · simp only [hstep, ↓reduceIte] at hnz
          exact (hnz rfl).elim
      · exact (hnz (matrix_internal_different data G diagonal e f hef t u)).elim

theorem terminal_internal_zero_or_one (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hpositive : ∀ e, G.sign e = 1) (v : V) (e : E)
    (t : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    matrix data G diagonal (Sum.inl v) (Sum.inr ⟨e, t⟩) = 0 ∨
      matrix data G diagonal (Sum.inl v) (Sum.inr ⟨e, t⟩) = 1 := by
  rw [matrix_terminal_internal, hpositive]
  by_cases hf : t = first data e ∧ v = G.tail e
  · have hl : ¬(t = last data e ∧ v = G.head e) :=
      fun h => first_ne_last data e (hf.1.symm.trans h.1)
    rw [ite_eq_left hf, ite_eq_right hl]
    exact Or.inr (add_zero _)
  · simp only [hf, ↓reduceIte, zero_add]
    split_ifs <;> simp

/-- Positive original edges give only positive unit off-diagonal couplings
throughout the complete routed matrix. -/
theorem offdiagonal_zero_or_one (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hpositive : ∀ e, G.sign e = 1)
    (a b : Subdivision.Vertex data) (hab : a ≠ b) :
    matrix data G diagonal a b = 0 ∨ matrix data G diagonal a b = 1 := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      left
      exact Matrix.diagonal_apply_ne _ (fun h => hab (congrArg Sum.inl h))
    | inr b =>
      rcases b with ⟨e, t⟩
      exact terminal_internal_zero_or_one data G diagonal hpositive a e t
  | inr a =>
    rcases a with ⟨e, t⟩
    cases b with
    | inl b =>
      exact terminal_internal_zero_or_one data G diagonal hpositive b e t
    | inr b =>
      rcases b with ⟨f, u⟩
      by_cases hef : e = f
      · subst f
        rw [matrix_internal_same]
        split_ifs <;> simp
      · exact Or.inl (matrix_internal_different data G diagonal e f hef t u)

end Maxwell.Composition.SubdivisionSchur
