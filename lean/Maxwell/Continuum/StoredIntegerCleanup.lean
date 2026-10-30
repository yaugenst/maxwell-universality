import Maxwell.Continuum.StoredIntegerSetup
import Maxwell.Continuum.RationalDataflowWordReplace

/-! Both serializer cursor words and the padded countdown are erased by
actual code, so a subsequent stream reuses the same fixed ports. -/
namespace Maxwell.Continuum.RationalDataflow.StoredInteger
open PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000

def clearPlan : List NatAssign.Instruction := [.literal 727 0,.literal 728 0]
def clearCode : Code := .seq (NatAssign.code clearPlan) (WordReplace.code 728 201)

theorem clear_executes (n : ℕ) (word : List Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (index : RationalAccumulator.Word s.val 728 n)
    (one : RationalAccumulator.Word s.val 727 1)
    (count : BankArray.Word s.val 201 word) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape clearCode cost s t ∧
      cost≤6*n.bits.length+6*word.length+64 ∧
      (∀i∈({201,727,728}:Finset ℕ),Blank t.val i) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (insert 201 controlChanged) s.val t.val := by
  have bank : NatAssign.Bank {727,728} (cursorValues n) s.val := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact one
    · have he : i=728 := Finset.mem_singleton.mp hi
      subst i
      exact index
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0⟩ := NatAssign.executes {727,728} (by
    intro i hi;simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    clearPlan (by simp [clearPlan,NatAssign.Instruction.Valid]) (cursorValues n) input tape s bank hz
  have zero0 (i : ℕ) (hi : i∈({727,728}:Finset ℕ)) : RationalAccumulator.Word s0.val i 0 := by
    rcases Finset.mem_insert.mp hi with rfl|hi
    · simpa [clearPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value] using b0 727 (by decide)
    · have he : i=728 := Finset.mem_singleton.mp hi
      subst i
      simpa [clearPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value] using b0 728 (by decide)
  have frame0 : BinaryPrecision.Frame controlChanged s.val s0.val := f0.mono (by decide)
  have count0 := BankArray.word_of_eq (frame0.tapes 201 (by decide)) count
  obtain ⟨t,e1,zero1,frame1⟩ := WordReplace.executes 728 201 (by decide) input tape [] word s0
    (zero0 728 (by decide)) count0
  have hprice : NatAssign.price clearPlan (cursorValues n)=6*n.bits.length+29 := by
    simp [clearPlan,NatAssign.price,NatAssign.Instruction.price,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,cursorValues]
    omega
  have f1 : BinaryPrecision.Frame {201} s0.val t.val :=
    ⟨frame1.1,frame1.2.1,frame1.2.2.1,frame1.2.2.2.1,frame1.2.2.2.2.1,
      fun i hi => frame1.2.2.2.2.2.1 i (by simpa only [Finset.mem_singleton] using hi)⟩
  refine ⟨c0+(6*word.length+15*([].length)+21),t,e0.seq e1,?_,?_,?_,
    (frame0.mono (by decide)).trans (f1.mono (by decide))⟩
  · rw [hprice] at hc0
    simp only [List.length_nil]
    omega
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · exact (RationalAccumulator.zero_word_iff_blank _ _).mp zero1
    · exact RationalAccumulator.blank_of_eq (f1.tapes 727 (by decide))
        ((RationalAccumulator.zero_word_iff_blank _ _).mp (zero0 727 (by decide)))
    · exact RationalAccumulator.blank_of_eq (f1.tapes 728 (by decide))
        ((RationalAccumulator.zero_word_iff_blank _ _).mp (zero0 728 (by decide)))
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f1.tapes i (by simp only [Finset.mem_singleton];omega)) (z0 i hi)

#print axioms clear_executes
end Maxwell.Continuum.RationalDataflow.StoredInteger
