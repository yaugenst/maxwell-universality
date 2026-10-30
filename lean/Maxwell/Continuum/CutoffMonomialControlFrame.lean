import Maxwell.Continuum.CutoffMonomialPassFrame
import Maxwell.Continuum.RationalDataflowWordReplace

/-! The outer cached-polynomial index uses dedicated natural-number words.
Updating those words preserves both table headers and the rational bank. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000

def monomialControlPorts : Finset ℕ := {0,1,2,3,201,206,207,208,209}

theorem monomialControl_rational_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s) (f : BinaryPrecision.Frame monomialControlPorts s.val t.val)
    (hz : NatAssign.Scratch t.val) : RationalDataflow.Ready S v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hge := ids_ge_ten S i hi
  apply RationalAccumulator.word_of_eq (f.tapes i _) (h.1 i hi)
  intro he
  have hiw : i∈workspace S := Finset.mem_union_right _ hi
  simp only [monomialControlPorts,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with he | he | he | he | he | he | he | he | he <;> subst i
  · omega
  · omega
  · omega
  · omega
  · exact outside_workspace S 201 (by decide) hiw
  · exact outside_workspace S 206 (by decide) hiw
  · exact outside_workspace S 207 (by decide) hiw
  · exact outside_workspace S 208 (by decide) hiw
  · exact outside_workspace S 209 (by decide) hiw

theorem monomialControl_table_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : BinaryPrecision.Frame monomialControlPorts s.val t.val)
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

theorem monomialControl_output_frame {n : ℕ} {a : Table n} {s t : Store}
    (h : a.OutputReady s) (f : BinaryPrecision.Frame monomialControlPorts s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  apply f.tapes i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def monomialIncrementCode : Code := (NatAssign.Instruction.add 209 208).code

theorem monomialIncrement_executes (j : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hj : RationalAccumulator.Word s.val 208 j) (h1 : RationalAccumulator.Word s.val 209 1)
    (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape monomialIncrementCode cost s t ∧
      cost≤200*(j.bits.length+5) ∧ RationalAccumulator.Word t.val 208 (j+1) ∧
      RationalAccumulator.Word t.val 209 1 ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changed 208) s.val t.val := by
  let v : ℕ→ℕ := fun i => if i=208 then j else 1
  have hb : NatAssign.Bank {208,209} v s.val := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa only [v,ite_true] using hj
    · simpa only [v,ite_eq_right (by decide : (209:ℕ)≠208)] using h1
  obtain ⟨cost,t,ex,hc,bt,zt,ft⟩ := NatAssign.instruction_executes {208,209}
    (by intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    (.add 209 208) (by simp [NatAssign.Instruction.Valid]) v input tape s hb hz
  refine ⟨cost,t,ex,?_,?_,?_,zt,ft⟩
  · simpa [NatAssign.Instruction.price,v,Nat.add_comm,Nat.add_assoc] using hc
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      v,Nat.add_comm] using bt 208 (by simp)
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,v] using bt 209 (by simp)

theorem monomialIncrement_frame {s t : Store}
    (f : BinaryPrecision.Frame (NatAssign.changed 208) s.val t.val) :
    BinaryPrecision.Frame monomialControlPorts s.val t.val := by
  apply f.mono
  simp [NatAssign.changed,monomialControlPorts]

#print axioms monomialIncrement_executes
end Maxwell.Continuum.Calibration.RawCutoff
