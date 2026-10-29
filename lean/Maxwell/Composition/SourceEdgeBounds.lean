import Maxwell.Composition.SourceEdgeList

/-! Output-size bound for the actual chronological edge list. This counts
emitted entries only; execution costs are attached by the finite backend. -/
namespace Maxwell.Composition.SourceEdgeList
open Maxwell.Logical Maxwell.Logical.Routing

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ k) : (xs.flatMap f).length ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (List.mem_cons_self)
    have hx := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    change (f a ++ xs.flatMap f).length ≤ (xs.length + 1) * k
    rw [List.length_append, Nat.add_mul, Nat.one_mul]
    omega

theorem length_le (S : Source.SparseSystem) (precision : ℕ) :
    (edges S precision).length ≤
      ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) *
        (1024 * (2 * portHalfSide ((sourceCircuit S precision).size +
          (sourceCircuit S precision).size + (sourceSquareEntries S precision).length))) := by
  rw [edges, List.length_map]
  unfold SourceSegmentList.raw
  apply (flatMap_length_le _ _
    (1024 * (2 * portHalfSide ((sourceCircuit S precision).size +
      (sourceCircuit S precision).size + (sourceSquareEntries S precision).length))) ?_).trans_eq
  · simp only [List.length_finRange]
  · intro e _
    rw [Segments.length]
    have h := SourceEmission.path_length_le S precision e
    omega

end Maxwell.Composition.SourceEdgeList
