import Maxwell.Composition.SubdivisionSteps

/-! Every actual off-diagonal matrix nonzero is a chronological path step,
and two distinct steps cannot represent the same undirected edge. -/

noncomputable section
namespace Maxwell.Composition.SubdivisionSteps
open Maxwell.Logical.Routing

variable {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)

def Matches (a b : Subdivision.Vertex data) (s : Step data) : Prop :=
  (a = left data s ∧ b = right data s) ∨ (a = right data s ∧ b = left data s)

theorem Matches.swap {a b : Subdivision.Vertex data} {s : Step data}
    (h : Matches data a b s) : Matches data b a s := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem internal_has_step (e : E) (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ∃ s : Step data, Matches data (.inr ⟨e, i⟩) (.inr ⟨e, j⟩) s := by
  suffices hforward : ∀ (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1)),
      i.val + 1 = j.val → ∃ s : Step data,
        left data s = .inr ⟨e, i⟩ ∧ right data s = .inr ⟨e, j⟩ by
    rcases hij with hij | hji
    · obtain ⟨s, hs⟩ := hforward i j hij
      exact ⟨s, Or.inl ⟨hs.1.symm, hs.2.symm⟩⟩
    · obtain ⟨s, hs⟩ := hforward j i hji
      exact ⟨s, Or.inr ⟨hs.2.symm, hs.1.symm⟩⟩
  intro i j hij
  have ht : i.val + 1 < (EdgeWalk.edgeWalk data e).length := by have := i.isLt; omega
  refine ⟨⟨e, ⟨i.val + 1, ht⟩⟩, at_internal data e i, ?_⟩
  change vertexAt data e (⟨i.val + 1, ht⟩ : Fin (EdgeWalk.edgeWalk data e).length).succ = _
  rw [show (⟨i.val + 1, ht⟩ : Fin (EdgeWalk.edgeWalk data e).length).succ =
      ⟨j.val + 1, by have := j.isLt; omega⟩ by apply Fin.ext; simp only [Fin.val_succ]; omega]
  exact at_internal data e j

variable [DecidableEq V] [DecidableEq E]
variable (G : SignedIncidence V E) (diagonal : V → ℝ)
variable (htail : ∀ e, G.tail e = data.endpoint e false)
variable (hhead : ∀ e, G.head e = data.endpoint e true)

include htail hhead in
theorem terminal_has_step (v : V) (e : E) (i : Fin ((EdgeWalk.edgeWalk data e).length - 1))
    (h : SubdivisionSchur.matrix data G diagonal (.inl v) (.inr ⟨e, i⟩) ≠ 0) :
    ∃ s : Step data, Matches data (.inl v) (.inr ⟨e, i⟩) s := by
  rw [SubdivisionSchur.matrix_terminal_internal] at h
  by_cases hf : i = SubdivisionSchur.first data e ∧ v = G.tail e
  · rcases hf with ⟨rfl, rfl⟩
    refine ⟨⟨e, ⟨0, by have := length_ge_five data e; omega⟩⟩, Or.inl ⟨?_, ?_⟩⟩
    · exact ((left_zero data e).trans (congrArg Sum.inl (htail e).symm)).symm
    · exact (right_zero data e).symm
  · have hl : i = SubdivisionSchur.last data e ∧ v = G.head e := by
      by_contra hn
      simp only [hf, hn, ↓reduceIte, add_zero] at h
      exact h rfl
    rcases hl with ⟨rfl, rfl⟩
    refine ⟨⟨e, ⟨(EdgeWalk.edgeWalk data e).length - 1, by
      have := length_ge_five data e; omega⟩⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact ((right_last data e).trans (congrArg Sum.inl (hhead e).symm)).symm
    · exact (left_last data e).symm

include htail hhead in
theorem matrix_support (a b : Subdivision.Vertex data) (hne : a ≠ b)
    (h : SubdivisionSchur.matrix data G diagonal a b ≠ 0) :
    ∃ s : Step data, Matches data a b s := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hab : a ≠ b := fun he => hne (congrArg Sum.inl he)
      have hz : SubdivisionSchur.matrix data G diagonal (.inl a) (.inl b) = 0 :=
        Matrix.diagonal_apply_ne _ hab
      exact (h hz).elim
    | inr b =>
      rcases b with ⟨e, i⟩
      exact terminal_has_step data G diagonal htail hhead a e i h
  | inr a =>
    rcases a with ⟨e, i⟩
    cases b with
    | inl b =>
      obtain ⟨s, hs⟩ := terminal_has_step data G diagonal htail hhead b e i h
      exact ⟨s, hs.swap data⟩
    | inr b =>
      rcases b with ⟨f, j⟩
      by_cases hef : e = f
      · subst f
        rw [SubdivisionSchur.matrix_internal_same] at h
        have hij : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
          by_contra hn
          simp only [hn, ↓reduceIte] at h
          exact h rfl
        exact internal_has_step data e i j hij
      · exact (h (SubdivisionSchur.matrix_internal_different data G diagonal e f hef i j)).elim

end Maxwell.Composition.SubdivisionSteps
