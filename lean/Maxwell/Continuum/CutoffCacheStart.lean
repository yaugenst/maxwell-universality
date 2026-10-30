import Maxwell.Continuum.CutoffMonomialOuterLoop
import Maxwell.Continuum.RationalDataflowStoredParts

/-! The outer recurrence receives its saved count, countdown and initial
index through actual runtime copies and a literal constant write. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def cacheStartCode : Code := .seq (WordReplace.code 720 206)
  (.seq (WordReplace.code 720 207) (NatAssign.Instruction.literal 209 1).code)

theorem cacheStart_executes {D W : ℕ} (a : MonomialCache D)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (s : Store)
    (hwidth : word.length≤monomialWorkingWidth D W)
    (hb : RationalDataflow.Ready (Finset.range 8) a.bank s)
    (ha : a.current.Ready s) (ho : a.spare.OutputReady s)
    (hindex : ∀i∈RowIndex.ids,Blank s.val i) (hswap : Blank s.val 216)
    (hcount : BankArray.Word s.val 201 word)
    (hdegree : RationalAccumulator.Word s.val 720 D)
    (hclean : ∀i∈({206,207,208,209}:Finset ℕ),Blank s.val i) :
    ∃cost t,Executes input tape cacheStartCode cost s t ∧ cost≤30*D.bits.length+2048 ∧
      a.Ready W 0 D.bits t ∧ RationalAccumulator.Word t.val 207 D ∧
      BinaryPrecision.Frame monomialControlPorts s.val t.val := by
  have b206 : BankArray.Word s.val 206 [] := by
    exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (hclean 206 (by decide))
  obtain ⟨s0,e0,saved0,f0⟩ := WordReplace.executes 720 206 (by decide) input tape D.bits [] s hdegree b206
  have f0' : BinaryPrecision.Frame monomialControlPorts s.val s0.val :=
    (StoredParts.copy_frame f0).mono (by decide)
  have degree0 := RationalAccumulator.word_of_eq (f0.2.2.2.2.2.1 720 (by decide)) hdegree
  have b207 : BankArray.Word s0.val 207 [] :=
    (RationalAccumulator.zero_word_iff_blank _ _).mpr (RationalAccumulator.blank_of_eq
      (f0.2.2.2.2.2.1 207 (by decide)) (hclean 207 (by decide)))
  obtain ⟨s1,e1,count1,f1⟩ := WordReplace.executes 720 207 (by decide) input tape D.bits [] s0 degree0 b207
  have f1' : BinaryPrecision.Frame monomialControlPorts s0.val s1.val :=
    (StoredParts.copy_frame f1).mono (by decide)
  let old : ℕ→ℕ := fun _ => 0
  have bank1 : NatAssign.Bank {209} old s1.val := by
    intro i hi
    have he : i=209 := Finset.mem_singleton.mp hi
    subst i
    exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (RationalAccumulator.blank_of_eq
      ((f1.2.2.2.2.2.1 209 (by decide)).trans (f0.2.2.2.2.2.1 209 (by decide))) (hclean 209 (by decide)))
  have scratch1 : NatAssign.Scratch s1.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq ((f1.2.2.2.2.2.1 i (by omega)).trans
      (f0.2.2.2.2.2.1 i (by omega))) (hb.2 i hi)
  obtain ⟨c2,t,e2,hc2,bank2,z2,f2⟩ := NatAssign.instruction_executes {209}
    (by intro i hi;have he := Finset.mem_singleton.mp hi;omega)
    (.literal 209 1) (by simp [NatAssign.Instruction.Valid]) old input tape s1 bank1 scratch1
  have f2' : BinaryPrecision.Frame monomialControlPorts s1.val t.val := f2.mono (by decide)
  have frame := f0'.trans (f1'.trans f2')
  have current := monomialControl_table_frame ha frame z2
  have ready : a.Ready W 0 D.bits t := by
    refine ⟨monomialControl_rational_frame hb frame z2,current,
      monomialControl_output_frame ho frame current.scratch current.seven,?_,
      RationalAccumulator.blank_of_eq (frame.tapes 216 (by decide)) hswap,?_,
      ⟨word,hwidth,BankArray.word_of_eq (by
        exact (f2.tapes 201 (by decide)).trans ((f1.2.2.2.2.2.1 201 (by decide)).trans
          (f0.2.2.2.2.2.1 201 (by decide)))) hcount⟩,?_,?_⟩
    · intro i hi
      apply RationalAccumulator.blank_of_eq (frame.tapes i _) (hindex i hi)
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl <;> decide
    · exact BankArray.word_of_eq ((f2.tapes 206 (by decide)).trans
        (f1.2.2.2.2.2.1 206 (by decide))) saved0
    · exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (RationalAccumulator.blank_of_eq
        ((f2.tapes 208 (by decide)).trans ((f1.2.2.2.2.2.1 208 (by decide)).trans
          (f0.2.2.2.2.2.1 208 (by decide)))) (hclean 208 (by decide)))
    · simpa only [NatAssign.Instruction.update,NatAssign.Instruction.target,
        NatAssign.Instruction.value,Function.update_self] using bank2 209 (by decide)
  refine ⟨_,t,e0.seq (e1.seq e2),?_,ready,
    BankArray.word_of_eq (f2.tapes 207 (by decide)) count1,frame⟩
  norm_num [NatAssign.Instruction.price,old] at hc2
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add]
  omega

#print axioms cacheStart_executes
end Maxwell.Continuum.Calibration.RawCutoff
