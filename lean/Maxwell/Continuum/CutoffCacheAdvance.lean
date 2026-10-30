import Maxwell.Continuum.CutoffCacheAllocationFrame

/-! Moving the cache allocator to its computed second buffer is one charged
runtime word copy. Both live tables and all rational registers persist. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def cacheAdvanceCode : Code := (NatAssign.Instruction.copy 729 727).code

theorem cacheAdvance_executes (heap next : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hheap : RationalAccumulator.Word s.val 727 heap)
    (hnext : RationalAccumulator.Word s.val 729 next) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape cacheAdvanceCode cost s t ∧
      cost≤200*(heap.bits.length+next.bits.length+3) ∧
      RationalAccumulator.Word t.val 727 next ∧ RationalAccumulator.Word t.val 729 next ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changed 727) s.val t.val := by
  let v : ℕ→ℕ := fun i => if i=727 then heap else next
  have bank : NatAssign.Bank {727,729} v s.val := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · simpa only [v,ite_true] using hheap
    · simpa only [v,ite_eq_right (by decide : (729:ℕ)≠727)] using hnext
  obtain ⟨cost,t,e,hc,b,z,f⟩ := NatAssign.instruction_executes {727,729}
    (by intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    (.copy 729 727) (by simp [NatAssign.Instruction.Valid]) v input tape s bank hz
  refine ⟨cost,t,e,?_,?_,?_,z,f⟩
  · simp [NatAssign.Instruction.price,v] at hc
    omega
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,v] using
      b 727 (by decide)
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,v] using b 729 (by decide)

theorem cacheAdvance_rational_frame {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready (Finset.range 8) v s)
    (f : BinaryPrecision.Frame (NatAssign.changed 727) s.val t.val) (z : NatAssign.Scratch t.val) :
    RationalDataflow.Ready (Finset.range 8) v t := by
  refine ⟨?_,z⟩
  have hd : Disjoint (ids (Finset.range 8)) (NatAssign.changed 727) := by decide
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.1 i hi)

theorem cacheAdvance_table_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame (NatAssign.changed 727) s.val t.val)
    (z : NatAssign.Scratch t.val) : a.Ready t := by
  refine ⟨⟨z 0 (by decide),z 1 (by decide),z 2 (by decide),z 3 (by decide),?_,?_,?_,?_⟩,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) h.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) h.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) h.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) h.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (f.tapes 7 (by decide)) h.seven
  · exact BankArray.word_of_eq (f.tapes 200 (by decide)) h.width
  · exact BankArray.word_of_eq (f.tapes 202 (by decide)) h.basePositive
  · exact BankArray.word_of_eq (f.tapes 203 (by decide)) h.baseNegative
  · exact BankArray.word_of_eq (f.tapes 204 (by decide)) h.baseDenominator
  · exact BankArray.word_of_eq (f.tapes 205 (by decide)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem cacheAdvance_output_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame (NatAssign.changed 727) s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  apply f.tapes i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms cacheAdvance_executes
end Maxwell.Continuum.Calibration.RawCutoff
