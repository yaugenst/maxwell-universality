import Maxwell.Continuum.RationalDataflowProgram
import Maxwell.Cost.BankArray.ReadCanonical

/-! Uniform indexed input to shared arithmetic registers. Indices and word widths are runtime data. -/

namespace Maxwell.Continuum.RationalDataflow.ArrayRead
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def code (widthBank indexBank baseBank clockBank target : ℕ) : Code :=
  .seq (NatAssign.Instruction.literal target 0).code
    (BankArray.readCanonicalCode widthBank indexBank baseBank clockBank target)

structure Frame (target : ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ i, 10 ≤ i → i≠target → t.tapes i=s.tapes i

theorem executes {n : ℕ} (allIds : Finset ℕ) (hids : ∀ i∈allIds, 10 ≤ i)
    (widthBank indexBank baseBank clockBank target : ℕ)
    (hw : 10≤widthBank) (hi : 10 ≤ indexBank) (hb : 10≤baseBank) (hc : 10≤clockBank)
    (ht : target∈allIds)
    (hwt : widthBank≠target) (hit : indexBank≠target) (hbt : baseBank≠target) (hct : clockBank≠target)
    (input : List Bool) (tape : ℕ→Bool) (width index base clock : List Bool)
    (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0<width.length) (hindex : addressValue index=i.val) (hclock : clock.length=addressValue width)
    (v : ℕ→ℕ) (s : Store) (hbank : NatAssign.Bank allIds v s.val)
    (hscratch : BankArray.Scratch s.val) (h7 : RationalAccumulator.Blank s.val 7)
    (hwidthBank : BankArray.Word s.val widthBank width) (hindexBank : BankArray.Word s.val indexBank index)
    (hbaseBank : BankArray.Word s.val baseBank base) (hclockBank : BankArray.Word s.val clockBank clock)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t,
      Executes input tape (code widthBank indexBank baseBank clockBank target) cost s t ∧
      cost≤6*(v target).bits.length+BankArray.costCap width index base clock+32*addressValue width+46 ∧
      NatAssign.Bank allIds (Function.update v target (addressValue (words.get i))) t.val ∧
      BankArray.Scratch t.val ∧ RationalAccumulator.Blank t.val 7 ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) words ∧ Frame target s.val t.val := by
  have hnat : NatAssign.Scratch s.val := by
    intro k hk
    interval_cases k
    · exact hscratch.1
    · exact hscratch.2.1
    · exact hscratch.2.2.1
    · exact hscratch.2.2.2.1
  obtain ⟨c0,r,e0,h0,b0,z0,f0⟩ := NatAssign.instruction_executes allIds
    (fun k hk => (by omega : 4≤10).trans (hids k hk)) (.literal target 0) ht v input tape s hbank hnat
  have keep (k : ℕ) (hk : 4 ≤ k) (hkt : k≠target) : r.val.tapes k=s.val.tapes k :=
    f0.tapes k (by simp only [NatAssign.changed, NatAssign.Instruction.target, Finset.mem_insert,Finset.mem_singleton]; omega)
  have rScratch : BankArray.Scratch r.val :=
    ⟨z0 0 (by decide),z0 1 (by decide),z0 2 (by decide),z0 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by have := hids target ht; omega)) hscratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by have := hids target ht; omega)) hscratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by have := hids target ht; omega)) hscratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by have := hids target ht; omega)) hscratch.2.2.2.2.2.2.2⟩
  have r7 : RationalAccumulator.Blank r.val 7 :=
    RationalAccumulator.blank_of_eq (keep 7 (by decide) (by have := hids target ht; omega)) h7
  have rTarget : RationalAccumulator.Blank r.val target := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      Function.update_self] using b0 target ht
  obtain ⟨c1,t,h1,e1,word1,z1,t7,mem1,array1,f1⟩ := BankArray.read_canonical
    widthBank indexBank baseBank clockBank target hw hi hb hc (hids target ht)
    input tape width index base clock words i hwidth hindex hclock r rScratch r7 rTarget
    (BankArray.word_of_eq (keep widthBank (by omega) hwt) hwidthBank)
    (BankArray.word_of_eq (keep indexBank (by omega) hit) hindexBank)
    (BankArray.word_of_eq (keep baseBank (by omega) hbt) hbaseBank)
    (BankArray.word_of_eq (keep clockBank (by omega) hct) hclockBank)
    (by simpa only [f0.memory] using harray)
  refine ⟨c0+c1,t,e0.seq e1,?_,?_,z1,t7,array1,?_⟩
  · change c0≤6*(v target).bits.length+11 at h0
    omega
  · intro k hk
    by_cases hkt : k=target
    · subst k; simpa only [Function.update_self] using word1
    · have hkeep := f1.2.2.2.1 k (Or.inr (hids k hk)) hkt
      have hword := RationalAccumulator.word_of_eq hkeep (b0 k hk)
      simpa only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
        Function.update_of_ne hkt] using hword
  · exact ⟨mem1.trans f0.memory,f1.1.trans f0.inputHead,f1.2.1.trans f0.randomCursor,
      f1.2.2.1.trans f0.output,fun k hk hkt =>
        (f1.2.2.2.1 k (Or.inr hk) hkt).trans (keep k (by omega) hkt)⟩

#print axioms executes

end Maxwell.Continuum.RationalDataflow.ArrayRead
