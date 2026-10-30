import Maxwell.Continuum.StoredIntegerCursor

/-! The serializer's only natural registers are initialized by fixed
instructions. Their initial blanks are the concrete phase-boundary contract. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000

def setupPlan : List NatAssign.Instruction := [.literal 727 1,.literal 728 0]
def setupCode : Code := NatAssign.code setupPlan
def controlChanged : Finset ℕ := {0,1,2,3,727,728}

theorem setup_executes (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h727 : Blank s.val 727) (h728 : Blank s.val 728) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape setupCode cost s t ∧ cost≤1024 ∧
      RationalAccumulator.Word t.val 727 1 ∧ RationalAccumulator.Word t.val 728 0 ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame controlChanged s.val t.val := by
  have bank : NatAssign.Bank {727,728} (fun _ => 0) s.val := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h727
    · have he : i=728 := Finset.mem_singleton.mp hi
      subst i
      exact (RationalAccumulator.zero_word_iff_blank _ _).mpr h728
  obtain ⟨cost,t,ex,hc,bt,zt,ft⟩ := NatAssign.executes {727,728} (by
    intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    setupPlan (by simp [setupPlan,NatAssign.Instruction.Valid]) (fun _ => 0) input tape s bank hz
  refine ⟨cost,t,ex,hc.trans ?_,?_,?_,zt,ft.mono ?_⟩
  · decide
  · simpa [setupPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using bt 727 (by decide)
  · simpa [setupPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using bt 728 (by decide)
  · decide

theorem ready_control_frame {v : ℕ→Parts} {s t : Store} (h : Ready slots v s)
    (f : BinaryPrecision.Frame controlChanged s.val t.val) (hz : NatAssign.Scratch t.val) : Ready slots v t := by
  refine ⟨?_,hz⟩
  have hd : Disjoint (ids slots) controlChanged := by decide
  intro i hi
  exact RationalAccumulator.word_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.1 i hi)

theorem table_control_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame controlChanged s.val t.val) (hz : NatAssign.Scratch t.val) : a.Ready t := by
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

#print axioms setup_executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
