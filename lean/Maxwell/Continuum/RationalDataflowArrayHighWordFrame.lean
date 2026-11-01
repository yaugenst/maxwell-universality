import Maxwell.Continuum.RationalDataflowArrayTransfer

/-! A memory-preserving update to a high auxiliary word preserves both
rational-array descriptor banks and the low arithmetic scratch tapes. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured

theorem arrays_high_word {T U port : ℕ} {a : Table T} {b : Table U} {s t : Store}
    (high : 216≤port) (cache : a.Ready s) (output : b.OutputReady s)
    (frame : BinaryPrecision.Frame {port} s.val t.val) : a.Ready t ∧ b.OutputReady t := by
  have keep (i : ℕ) (hi : i<216) := frame.tapes i (by simp;omega)
  have z : BankArray.Scratch t.val :=
    ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) cache.scratch.1,
     RationalAccumulator.blank_of_eq (keep 1 (by decide)) cache.scratch.2.1,
     RationalAccumulator.blank_of_eq (keep 2 (by decide)) cache.scratch.2.2.1,
     RationalAccumulator.blank_of_eq (keep 3 (by decide)) cache.scratch.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 5 (by decide)) cache.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 6 (by decide)) cache.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 8 (by decide)) cache.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq (keep 9 (by decide)) cache.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq (keep 7 (by decide)) cache.seven
  constructor
  · apply cache.transfer frame.memory _ z seven
    intro i hi
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  · apply output.transfer frame.memory _ z seven
    intro i hi
    apply keep
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega

#print axioms arrays_high_word
end Maxwell.Continuum.RationalDataflow.PartArray
