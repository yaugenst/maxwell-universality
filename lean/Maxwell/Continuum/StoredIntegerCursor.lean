import Maxwell.Continuum.StoredIntegerEmission
import Maxwell.Continuum.NaturalBankStage

/-! The serializer advances an actual stored natural index by one. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000

def cursorValues (j : ℕ) (i : ℕ) : ℕ := if i=728 then j else 1
def advanceCode : Code := (NatAssign.Instruction.add 727 728).code

theorem advance_executes (j B : ℕ) (hj : j.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (index : RationalAccumulator.Word s.val 728 j)
    (one : RationalAccumulator.Word s.val 727 1) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape advanceCode cost s t ∧ cost≤2^14*(B+3)^2 ∧
      RationalAccumulator.Word t.val 728 (j+1) ∧ RationalAccumulator.Word t.val 727 1 ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changed 728) s.val t.val := by
  have bank : NatAssign.Bank {727,728} (cursorValues j) s.val := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact one
    · exact index
  obtain ⟨cost,t,ex,hcost,bt,zt,ft⟩ := NatAssign.instruction_executes {727,728} (by
      intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    (.add 727 728) (by simp [NatAssign.Instruction.Valid]) (cursorValues j) input tape s bank hz
  refine ⟨cost,t,ex,hcost.trans ?_,?_,?_,zt,ft⟩
  · simp only [NatAssign.Instruction.price,cursorValues,ite_true,
      ite_eq_right (by decide : (727:ℕ)≠728),show (1:ℕ).bits.length=1 from rfl]
    nlinarith only [hj,Nat.zero_le B]
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,cursorValues,Nat.add_comm] using bt 728 (by decide)
  · simpa [NatAssign.Instruction.update,NatAssign.Instruction.target,
      cursorValues] using bt 727 (by decide)

theorem ready_advance_frame {v : ℕ→Parts} {s t : Store} (h : Ready slots v s)
    (f : BinaryPrecision.Frame (NatAssign.changed 728) s.val t.val) (hz : NatAssign.Scratch t.val) :
    Ready slots v t := by
  refine ⟨?_,hz⟩
  have disjoint : Disjoint (ids slots) (NatAssign.changed 728) := by decide
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hh => Finset.disjoint_left.mp disjoint hi hh)) (h.1 i hi)

theorem table_advance_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame (NatAssign.changed 728) s.val t.val) (hz : NatAssign.Scratch t.val) :
    a.Ready t := by
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

#print axioms advance_executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
