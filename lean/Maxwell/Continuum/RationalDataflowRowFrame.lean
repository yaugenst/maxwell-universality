import Maxwell.Continuum.RationalDataflowIndexArithmetic

/-! The dedicated row-index arithmetic preserves rational registers,
cached tables and the outer countdown, and its three temporary words
can be cleared by a fixed charged program. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray.RowIndex
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem rationalReady_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : RationalDataflow.Ready S v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hge := ids_ge_ten S i hi
  have hout : i∉changed := by
    intro he
    simp only [changed,Finset.mem_insert,Finset.mem_singleton] at he
    have hiw : i∈workspace S := Finset.mem_union_right _ hi
    rcases he with he | he | he | he | he | he | he <;> subst i
    · omega
    · omega
    · omega
    · omega
    · exact outside_workspace S 220 (by decide) hiw
    · exact outside_workspace S 221 (by decide) hiw
    · exact outside_workspace S 222 (by decide) hiw
  exact RationalAccumulator.word_of_eq (f.tapes i hout) (h.1 i hi)

theorem tableReady_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame changed s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.Ready t := by
  refine ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),?_,?_,?_,?_⟩,
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

def clearInstructions : List NatAssign.Instruction := [.literal 220 0,.literal 221 0,.literal 222 0]

theorem clear_valid : ∀a∈clearInstructions,a.Valid ids := by
  simp [clearInstructions,NatAssign.Instruction.Valid,ids]

theorem clear_values (v : ℕ→ℕ) (i : ℕ) (hi : i∈ids) :
    NatAssign.values clearInstructions v i=0 := by
  simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;>
    simp [clearInstructions,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem clear_price (v : ℕ→ℕ) :
    NatAssign.price clearInstructions v=6*((v 220).bits.length+(v 221).bits.length+(v 222).bits.length)+34 := by
  simp [clearInstructions,NatAssign.price,NatAssign.Instruction.price,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  ring

theorem clear_executes (v : ℕ→ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code clearInstructions) cost s t ∧
      cost≤6*((v 220).bits.length+(v 221).bits.length+(v 222).bits.length)+34 ∧
      (∀i∈ids,RationalAccumulator.Blank t.val i) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cost,t,he,hc,hb',hz,hf⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    clearInstructions clear_valid v input tape s hb hs
  refine ⟨cost,t,he,by simpa only [clear_price] using hc,?_,hz,?_⟩
  · intro i hi
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [clear_values v i hi] using hb' i hi
  · exact hf.mono (by
      intro i hi
      simp only [NatAssign.changes,clearInstructions,NatAssign.Instruction.target,List.map_cons,
        List.map_nil,List.toFinset_cons,List.toFinset_nil,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,changed] at hi ⊢
      tauto)

#print axioms clear_executes
#print axioms rationalReady_frame
#print axioms tableReady_frame
end Maxwell.Continuum.RationalDataflow.PartArray.RowIndex
