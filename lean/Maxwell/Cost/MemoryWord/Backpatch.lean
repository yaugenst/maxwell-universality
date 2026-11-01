import Maxwell.Cost.MemoryWord.Write

/-! Exact memory algebra for writing a header after its payload. -/
namespace Maxwell.Cost.MemoryWord

theorem writeBits_update_outside (memory : ℕ→Bool) (address : ℕ) (bits : List Bool)
    (position : ℕ) (value : Bool) (outside : position<address ∨ address+bits.length ≤ position) :
    writeBits (Function.update memory position value) address bits=
      Function.update (writeBits memory address bits) position value := by
  induction bits generalizing memory address with
  | nil => rfl
  | cons bit bits ih =>
    simp only [writeBits]
    rw [Function.update_comm (by simp only [List.length_cons] at outside;omega : position≠address)]
    exact ih (Function.update memory address bit) (address+1)
      (by simp only [List.length_cons] at outside;omega)

/-- The header is written after the payload by the machine, but the resulting
memory is exactly the ordinary chronological header followed by payload. -/
theorem writeBits_prepend (memory : ℕ→Bool) (address : ℕ) (header payload : List Bool) :
    writeBits (writeBits memory (address+header.length) payload) address header=
      writeBits memory address (header++payload) := by
  induction header generalizing memory address with
  | nil => rfl
  | cons bit header ih =>
    simp only [List.length_cons,List.cons_append,writeBits]
    rw [←writeBits_update_outside memory (address+(header.length+1)) payload address bit (Or.inl (by omega))]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (Function.update memory address bit) (address+1)

#print axioms writeBits_prepend
end Maxwell.Cost.MemoryWord
