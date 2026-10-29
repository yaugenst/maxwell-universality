import Maxwell.Composition.SubdivisionLocality

/-! Chronological unit-edge indices for the actual routed source graph.
These indices are the finite compiler's sparse edge stream. -/

noncomputable section
namespace Maxwell.Composition.SubdivisionSteps
open Maxwell.Logical.Routing
open scoped BigOperators

variable {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)

abbrev Step := Σ e : E, Fin ((EdgeWalk.edgeWalk data e).length)

theorem length_ge_five (e : E) : 5 ≤ (EdgeWalk.edgeWalk data e).length := by
  obtain ⟨j, hj, he⟩ := Subdivision.internal_count_positive_wire_form data e
  change (EdgeWalk.edgeWalk data e).length - 1 = 4 * j at he
  omega

abbrev vertexAt (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length + 1)) :
    Subdivision.Vertex data := Subdivision.edgeVertex data e t

theorem at_zero (e : E) :
    vertexAt data e ⟨0, by omega⟩ = .inl (data.endpoint e false) := by
  simp only [vertexAt, Subdivision.edgeVertex, ↓reduceDIte]
  rfl

theorem at_last (e : E) :
    vertexAt data e ⟨(EdgeWalk.edgeWalk data e).length, by omega⟩ =
      .inl (data.endpoint e true) := by
  have h0 : (EdgeWalk.edgeWalk data e).length ≠ 0 := by have := length_ge_five data e; omega
  simp only [vertexAt, Subdivision.edgeVertex, h0, ↓reduceDIte]
  rfl

theorem at_internal (e : E)
    (i : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    vertexAt data e ⟨i.val + 1, by have := i.isLt; omega⟩ = .inr ⟨e, i⟩ := by
  have h0 : i.val + 1 ≠ 0 := by omega
  have hl : i.val + 1 ≠ (EdgeWalk.edgeWalk data e).length := by have := i.isLt; omega
  simp only [vertexAt, Subdivision.edgeVertex, h0, hl, ↓reduceDIte, Nat.add_sub_cancel]
  rfl

def left (s : Step data) : Subdivision.Vertex data := vertexAt data s.1 s.2.castSucc
def right (s : Step data) : Subdivision.Vertex data := vertexAt data s.1 s.2.succ

theorem left_zero (e : E) :
    left data ⟨e, ⟨0, by have := length_ge_five data e; omega⟩⟩ =
      .inl (data.endpoint e false) := at_zero data e

theorem right_last (e : E) :
    right data ⟨e, ⟨(EdgeWalk.edgeWalk data e).length - 1, by have := length_ge_five data e; omega⟩⟩ =
      .inl (data.endpoint e true) := by
  have he : (EdgeWalk.edgeWalk data e).length - 1 + 1 = (EdgeWalk.edgeWalk data e).length := by
    have := length_ge_five data e
    omega
  change vertexAt data e (⟨(EdgeWalk.edgeWalk data e).length - 1, _⟩ :
    Fin (EdgeWalk.edgeWalk data e).length).succ = _
  rw [show (⟨(EdgeWalk.edgeWalk data e).length - 1, by have := length_ge_five data e; omega⟩ :
      Fin (EdgeWalk.edgeWalk data e).length).succ =
        ⟨(EdgeWalk.edgeWalk data e).length, by omega⟩ by apply Fin.ext; exact he]
  exact at_last data e

theorem left_internal (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length))
    (ht : 0 < t.val) : left data ⟨e, t⟩ =
      .inr ⟨e, ⟨t.val - 1, by have := t.isLt; omega⟩⟩ := by
  have he : t.val - 1 + 1 = t.val := by omega
  change vertexAt data e t.castSucc = _
  rw [show t.castSucc = (⟨t.val - 1 + 1, by have := t.isLt; omega⟩ :
    Fin ((EdgeWalk.edgeWalk data e).length + 1)) by apply Fin.ext; exact he.symm]
  exact at_internal data e ⟨t.val - 1, by have := t.isLt; omega⟩

theorem right_internal (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length))
    (ht : t.val + 1 < (EdgeWalk.edgeWalk data e).length) : right data ⟨e, t⟩ =
      .inr ⟨e, ⟨t.val, by omega⟩⟩ := at_internal data e ⟨t.val, by omega⟩


theorem right_zero (e : E) :
    right data ⟨e, ⟨0, by have := length_ge_five data e; omega⟩⟩ =
      .inr ⟨e, SubdivisionSchur.first data e⟩ := by
  rw [right_internal data e _ (by have := length_ge_five data e; simp only; omega)]
  rfl

theorem left_last (e : E) :
    left data ⟨e, ⟨(EdgeWalk.edgeWalk data e).length - 1, by have := length_ge_five data e; omega⟩⟩ =
      .inr ⟨e, SubdivisionSchur.last data e⟩ := by
  rw [left_internal data e _ (by have := length_ge_five data e; simp only; omega)]
  have he : (⟨(EdgeWalk.edgeWalk data e).length - 1 - 1, by
      have := length_ge_five data e; omega⟩ : Fin ((EdgeWalk.edgeWalk data e).length - 1)) =
        SubdivisionSchur.last data e := by
    apply Fin.ext
    rw [SubdivisionSchur.last_val]
    simp only
    omega
  exact congrArg (fun i => (Sum.inr ⟨e, i⟩ : Subdivision.Vertex data)) he

theorem vertexAt_internal_edge (e : E) (t : Fin ((EdgeWalk.edgeWalk data e).length + 1))
    (f : E) (i : Fin ((EdgeWalk.edgeWalk data f).length - 1))
    (h : vertexAt data e t = .inr ⟨f, i⟩) : e = f := by
  by_cases h0 : t.val = 0
  · unfold vertexAt Subdivision.edgeVertex at h
    erw [dite_eq_left h0] at h
    cases h
  · by_cases hl : t.val = (EdgeWalk.edgeWalk data e).length
    · unfold vertexAt Subdivision.edgeVertex at h
      erw [dite_eq_right h0, dite_eq_left hl] at h
      cases h
    · unfold vertexAt Subdivision.edgeVertex at h
      erw [dite_eq_right h0, dite_eq_right hl] at h
      exact congrArg Sigma.fst (Sum.inr.inj h)

theorem one_internal (s : Step data) :
    ∃ i : Fin ((EdgeWalk.edgeWalk data s.1).length - 1),
      left data s = .inr ⟨s.1, i⟩ ∨ right data s = .inr ⟨s.1, i⟩ := by
  rcases s with ⟨e, t⟩
  dsimp only
  by_cases h : 0 < t.val
  · exact ⟨⟨t.val - 1, by have := t.isLt; omega⟩, Or.inl (left_internal data e t h)⟩
  · have ht : t.val + 1 < (EdgeWalk.edgeWalk data e).length := by
      have := length_ge_five data e
      omega
    exact ⟨⟨t.val, by omega⟩, Or.inr (right_internal data e t ht)⟩

/-- Even forgetting the orientation cannot identify two distinct path steps. -/
theorem unordered_injective (a b : Step data)
    (h : (left data a = left data b ∧ right data a = right data b) ∨
      (left data a = right data b ∧ right data a = left data b)) : a = b := by
  have he : b.1 = a.1 := by
    obtain ⟨i, hi | hi⟩ := one_internal data a
    · rcases h with h | h
      · exact vertexAt_internal_edge data b.1 b.2.castSucc a.1 i (h.1.symm.trans hi)
      · exact vertexAt_internal_edge data b.1 b.2.succ a.1 i (h.1.symm.trans hi)
    · rcases h with h | h
      · exact vertexAt_internal_edge data b.1 b.2.succ a.1 i (h.2.symm.trans hi)
      · exact vertexAt_internal_edge data b.1 b.2.castSucc a.1 i (h.2.symm.trans hi)
  rcases a with ⟨e, t⟩
  rcases b with ⟨f, u⟩
  dsimp only at he
  subst f
  rcases h with h | h
  · have ht := Subdivision.edgeVertex_injective data e h.1
    have hv : t.val = u.val := congrArg (fun k : Fin ((EdgeWalk.edgeWalk data e).length + 1) => k.val) ht
    have htu : t = u := Fin.ext hv
    subst u
    rfl
  · have ht := Subdivision.edgeVertex_injective data e h.1
    have hu := Subdivision.edgeVertex_injective data e h.2
    have htv := congrArg (fun k : Fin ((EdgeWalk.edgeWalk data e).length + 1) => k.val) ht
    have huv := congrArg (fun k : Fin ((EdgeWalk.edgeWalk data e).length + 1) => k.val) hu
    simp only [Fin.val_castSucc, Fin.val_succ] at htv huv
    omega

variable [DecidableEq V] [DecidableEq E]
variable (G : SignedIncidence V E) (diagonal : V → ℝ)
variable (htail : ∀ e, G.tail e = data.endpoint e false)
variable (hhead : ∀ e, G.head e = data.endpoint e true)
variable (hpositive : ∀ e, G.sign e = 1)

include htail hhead hpositive in
theorem matrix_step (s : Step data) :
    SubdivisionSchur.matrix data G diagonal (left data s) (right data s) = 1 := by
  rcases s with ⟨e, t⟩
  have hl := length_ge_five data e
  by_cases ht0 : t.val = 0
  · have ht : t = ⟨0, by omega⟩ := Fin.ext ht0
    rw [ht]
    rw [left_zero, right_internal data e _ (by simpa using (show 1 < (EdgeWalk.edgeWalk data e).length by omega))]
    rw [SubdivisionSchur.matrix_terminal_internal]
    have hf : (⟨0, by omega⟩ : Fin ((EdgeWalk.edgeWalk data e).length - 1)) =
        SubdivisionSchur.first data e := Fin.ext rfl
    have hn : (⟨0, by omega⟩ : Fin ((EdgeWalk.edgeWalk data e).length - 1)) ≠
        SubdivisionSchur.last data e := by
      intro h
      have hv := congrArg Fin.val h
      rw [SubdivisionSchur.last_val] at hv
      change 0 = (EdgeWalk.edgeWalk data e).length - 2 at hv
      omega
    rw [ite_eq_left (And.intro hf (htail e).symm),
      ite_eq_right (fun h => hn h.1), add_zero]
  · have htpos : 0 < t.val := by omega
    by_cases hlast : t.val + 1 = (EdgeWalk.edgeWalk data e).length
    · have ht : t = ⟨(EdgeWalk.edgeWalk data e).length - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [ht]
      rw [left_internal data e _ (by simp; omega), right_last]
      change SubdivisionSchur.matrix data G diagonal
        (.inl (data.endpoint e true)) (.inr _) = 1
      rw [SubdivisionSchur.matrix_terminal_internal]
      have hf : (⟨(EdgeWalk.edgeWalk data e).length - 1 - 1, by omega⟩ : Fin ((EdgeWalk.edgeWalk data e).length - 1)) ≠
          SubdivisionSchur.first data e := by
        intro h
        have hv := congrArg Fin.val h
        rw [SubdivisionSchur.first_val] at hv
        change (EdgeWalk.edgeWalk data e).length - 1 - 1 = 0 at hv
        omega
      have he : (⟨(EdgeWalk.edgeWalk data e).length - 1 - 1, by omega⟩ : Fin ((EdgeWalk.edgeWalk data e).length - 1)) =
          SubdivisionSchur.last data e := by
        apply Fin.ext
        rw [SubdivisionSchur.last_val]
        change (EdgeWalk.edgeWalk data e).length - 1 - 1 = (EdgeWalk.edgeWalk data e).length - 2
        omega
      rw [ite_eq_right (fun h => hf h.1),
        ite_eq_left (And.intro he (hhead e).symm), zero_add, hpositive]
    · have htlt : t.val + 1 < (EdgeWalk.edgeWalk data e).length := by have := t.isLt; omega
      rw [left_internal data e t htpos, right_internal data e t htlt]
      rw [SubdivisionSchur.matrix_internal_same]
      simp only [show t.val - 1 + 1 = t.val by omega, true_or, ↓reduceIte]

end Maxwell.Composition.SubdivisionSteps
