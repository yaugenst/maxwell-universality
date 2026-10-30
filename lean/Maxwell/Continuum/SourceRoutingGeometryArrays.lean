import Maxwell.Continuum.SourceRoutingArrayMachine

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArrays

def Stored {slots n : ℕ} (memory : ℕ→Bool) (base : Fin slots→ℕ) (width : ℕ)
    (arrays : Fin slots→Vector (List Bool) n) : Prop :=
  ∀slot,BitArray.Represents memory (base slot) width (arrays slot)

def Separated {slots : ℕ} (base : Fin slots→ℕ) (n width : ℕ) : Prop :=
  ∀a b,a≠b→IncidenceEncoding.Separated (base a) (n*width) (base b) (n*width)

theorem write {slots n width : ℕ} {memory : ℕ→Bool} {base : Fin slots→ℕ}
    {arrays : Fin slots→Vector (List Bool) n} (stored : Stored memory base width arrays)
    (separated : Separated base n width) (slot : Fin slots) (index : Fin n)
    (payload : List Bool) (length : payload.length=width) :
    Stored (MemoryWord.writeBits memory (base slot+index.val*width) payload) base width
      (Function.update arrays slot ((arrays slot).set index payload)) := by
  intro j
  by_cases he : j=slot
  · subst j
    rw [Function.update_self]
    exact (stored slot).write index payload length
  · rw [Function.update_of_ne he]
    exact IncidenceEncoding.represents_write_disjoint (stored j) (base slot) width index payload length
      (separated j slot he)

theorem snapshot {slots n width : ℕ} (memory : ℕ→Bool) (base : Fin slots→ℕ) :
    Stored memory base width (fun slot => GeometryArray.snapshot memory (base slot) width n) :=
  fun slot => GeometryArray.snapshot_represents memory (base slot) width n

#print axioms write
end Maxwell.Cost.RoutingPorts.Complete.GeometryArrays
