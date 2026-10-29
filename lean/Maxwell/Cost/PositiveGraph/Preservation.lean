import Maxwell.Cost.PositiveGraph.Fold

namespace Maxwell.Cost.PositiveGraph

/-- The actual seven writes leave the separately initialized routing
counter and rank arrays intact. -/
theorem entryMemory_preserves {n : ℕ} {memory : ℕ → Bool} {otherBase otherWidth : ℕ}
    {words : Vector (List Bool) n} (h : BitArray.Represents memory otherBase otherWidth words)
    (width dimension count index base : ℕ) (hi : index < count)
    (e : BoundedEntry dimension) (diagonal : Vector (List Bool) (2*dimension+count))
    (he : IncidenceEncoding.Separated otherBase (n*otherWidth) 0 (4*count*(width+3)))
    (hg : IncidenceEncoding.Separated otherBase (n*otherWidth) base ((2*dimension+count)*4)) :
    BitArray.Represents (entryMemory width dimension count index base hi e.val e.property.1 e.property.2
      diagonal memory) otherBase otherWidth words := by
  have h1 := Endpoints.writePair_preserves (m := 4*count) h (width+3) (2*index) (by omega)
    (SourceCircuit.fixedWidth width e.val.row) (2*dimension+index).bits he
  have h2 := Endpoints.writePair_preserves (m := 4*count) h1 (width+3) (2*(count+index)) (by omega)
    (dimension+e.val.column).bits (2*dimension+index).bits he
  exact TripleScatter.write_preserves h2 (rowIndex dimension count e.val e.property.1)
    (columnIndex dimension count e.val e.property.2) (mediatorIndex dimension count index hi)
    (codeAt diagonal (rowIndex dimension count e.val e.property.1))
    (codeAt diagonal (columnIndex dimension count e.val e.property.2))
    (codeAt diagonal (mediatorIndex dimension count index hi))
    (decide (e.val.value<0)) (decide (e.val.value=1/2 ∨ e.val.value= -1/2)) hg

theorem foldMemory_preserves {n : ℕ} {memory : ℕ → Bool} {otherBase otherWidth : ℕ}
    {words : Vector (List Bool) n} (h : BitArray.Represents memory otherBase otherWidth words)
    (width dimension count index base : ℕ) (entries : List (BoundedEntry dimension))
    (hfit : index+entries.length ≤ count) (tables : Tables dimension count)
    (he : IncidenceEncoding.Separated otherBase (n*otherWidth) 0 (4*count*(width+3)))
    (hg : IncidenceEncoding.Separated otherBase (n*otherWidth) base ((2*dimension+count)*4)) :
    BitArray.Represents (foldMemory width dimension count index base entries hfit tables memory)
      otherBase otherWidth words := by
  induction entries generalizing index tables memory with
  | nil => exact h
  | cons e rest ih =>
    have hi : index < count := by simp only [List.length_cons] at hfit; omega
    exact ih (entryMemory_preserves h width dimension count index base hi e tables.diagonal he hg)
      (index+1) (by simp only [List.length_cons] at hfit; omega) (tables.next width dimension count index hi e)

end Maxwell.Cost.PositiveGraph
