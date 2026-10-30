import Maxwell.Continuum.CalibrationInverseAllocationPlan
import Maxwell.Continuum.NatAssignOutputWidth

/-! The common-denominator destination is allocated by executed metadata
arithmetic and a counted width clock. Its uninitialized memory is read
only to state the actual starting buffer. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def code : Code := .seq (WordCleanup.code clearHeaders)
  (.seq (NatAssign.code plan) (WidthClock.code 301 216 215))

theorem cleared_width (v : ℕ → ℕ) (B : ℕ)
    (hv : ∀ i ∈ inputs, (v i).bits.length ≤ B) :
    ∀ i ∈ ids, (clearedValues v i).bits.length ≤ B := by
  intro i hi
  by_cases hh : i ∈ headerIds
  · simp [clearedValues,hh]
  · rw [clearedValues,ite_eq_right hh]
    exact hv i ((Finset.mem_union.mp hi).resolve_right hh)

theorem plan_keep (v : ℕ → ℕ) (i : ℕ) (hi : i ∉ targets) :
    NatAssign.values plan v i=v i := by
  have general (p : List NatAssign.Instruction) (v : ℕ → ℕ)
      (hp : ∀ a ∈ p, i ≠ a.target) : NatAssign.values p v i=v i := by
    induction p generalizing v with
    | nil => rfl
    | cons a rest ih =>
      rw [NatAssign.values,ih _ (fun b hb => hp b (by simp [hb])),NatAssign.Instruction.update,
        Function.update_of_ne (hp a (by simp))]
  exact general plan v (fun a ha he => hi (he ▸ target_mem a ha))

theorem executes {m p : ℕ} (a : PartArray.Table m) (old : PartArray.Table p)
    (v : ℕ → ℕ) (B H : ℕ) (hwidth : 0 < v 301)
    (hv : ∀ i ∈ inputs, (v i).bits.length ≤ B) (hmeta : old.MetadataWidth H)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank inputs v s.val) (ha : a.Ready s) (ho : old.OutputReady s)
    (h216 : Blank s.val 216) :
    ∃ cost t, Executes input tape code cost s t ∧
      cost ≤ 2^60*(B+H+v 301+3)^2 ∧ a.Ready t ∧
      (table (v 300) (v 301) (v 302) hwidth s.val.memory).OutputReady t ∧
      NatAssign.Bank ids (outputValues v) t.val ∧
      (∀ i ∈ ids, (outputValues v i).bits.length ≤ 2^14*(B+1)) ∧
      Blank t.val 216 ∧ BinaryPrecision.Frame changed s.val t.val := by
  have oldWords : WordCleanup.Bounded clearHeaders H s.val := by
    intro i hi
    simp only [clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · exact ⟨old.width,hmeta.width,ho.width⟩
    · exact ⟨old.basePositive,hmeta.basePositive,ho.basePositive⟩
    · exact ⟨old.baseNegative,hmeta.baseNegative,ho.baseNegative⟩
    · exact ⟨old.baseDenominator,hmeta.baseDenominator,ho.baseDenominator⟩
    · exact ⟨old.clock,hmeta.clock,ho.clock⟩
  obtain ⟨c0,u0,e0,hc0,z0,f0⟩ := WordCleanup.executes clearHeaders H input tape s oldWords
  have bank0 : NatAssign.Bank ids (clearedValues v) u0.val := by
    intro i hi
    by_cases hh : i ∈ headerIds
    · rw [clearedValues,ite_eq_left hh,RationalAccumulator.zero_word_iff_blank]
      apply z0
      simp only [headerIds,Finset.mem_insert,Finset.mem_singleton] at hh
      simp only [clearHeaders,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    · have hin := (Finset.mem_union.mp hi).resolve_right hh
      rw [clearedValues,ite_eq_right hh]
      apply RationalAccumulator.word_of_eq (f0.tapes i _) (hb i hin)
      simp only [inputs,Finset.mem_Icc] at hin
      simp only [List.mem_toFinset,clearHeaders,List.mem_cons,List.not_mem_nil,or_false]
      omega
  have scratch0 : NatAssign.Scratch u0.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i (by
      simp only [List.mem_toFinset,clearHeaders,List.mem_cons,List.not_mem_nil,or_false]; omega))
    interval_cases i
    · exact ha.scratch.1
    · exact ha.scratch.2.1
    · exact ha.scratch.2.2.1
    · exact ha.scratch.2.2.2.1
  have literals : ∀ ins ∈ plan, ins.literalWidth ≤ B := by simp [plan,NatAssign.Instruction.literalWidth]
  obtain ⟨c1,u1,e1,hc1,bank1,z1,f1⟩ := NatAssign.executes ids inputs_ge plan valid (clearedValues v)
    input tape u0 bank0 scratch0
  have price := hc1.trans (NatAssign.price_bound ids plan valid (clearedValues v) B
    (cleared_width v B hv) literals)
  have h301 : RationalAccumulator.Word u1.val 301 (v 301) := by
    have h := bank1 301 (by simp [ids,inputs])
    change RationalAccumulator.Word u1.val 301 (outputValues v 301) at h
    simpa only [(outputs v).2.2.2.2.2.2.1] using h
  have clock0 : Blank u1.val 215 := RationalAccumulator.blank_of_eq (f1.tapes 215 (by
    simp [NatAssign.changes,plan,NatAssign.Instruction.target])) (z0 215 (by simp [clearHeaders]))
  have temp0 : Blank u1.val 216 := RationalAccumulator.blank_of_eq
    ((f1.tapes 216 (by simp [NatAssign.changes,plan,NatAssign.Instruction.target])).trans
      (f0.tapes 216 (by simp [clearHeaders]))) h216
  obtain ⟨c2,t,e2,hc2,_,z216,clock,f2⟩ := WidthClock.executes 301 216 215
    (by decide) (by decide) (by decide) input tape (v 301).bits u1 h301 temp0 clock0
  rw [addressValue_bits] at hc2 clock
  have sub0 : clearHeaders.toFinset ⊆ changed := by decide
  have sub1 : NatAssign.changes plan ⊆ changed := by decide
  have sub2 : ({216,215}:Finset ℕ) ⊆ changed := by decide
  have frame := (f0.mono sub0).trans ((f1.mono sub1).trans (f2.mono sub2))
  have scratch : BankArray.Scratch t.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq (f2.tapes 0 (by decide)) (z1 0 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 1 (by decide)) (z1 1 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 2 (by decide)) (z1 2 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 3 (by decide)) (z1 3 (by decide))
    · exact RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) ha.scratch.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) ha.scratch.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) ha.scratch.2.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) ha.scratch.2.2.2.2.2.2.2
  have seven := RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) ha.seven
  have source : a.Ready t := by
    refine ⟨scratch,seven,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact BankArray.word_of_eq (frame.tapes 200 (by decide)) ha.width
    · exact BankArray.word_of_eq (frame.tapes 202 (by decide)) ha.basePositive
    · exact BankArray.word_of_eq (frame.tapes 203 (by decide)) ha.baseNegative
    · exact BankArray.word_of_eq (frame.tapes 204 (by decide)) ha.baseDenominator
    · exact BankArray.word_of_eq (frame.tapes 205 (by decide)) ha.clock
    · simpa only [frame.memory] using ha.positive
    · simpa only [frame.memory] using ha.negative
    · simpa only [frame.memory] using ha.denominator
  have bank : NatAssign.Bank ids (outputValues v) t.val := by
    intro i hi
    have hn : i ≠ 216 ∧ i ≠ 215 := by
      simp only [ids,inputs,headerIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.word_of_eq (f2.tapes i (by simp [hn.1,hn.2])) (bank1 i hi)
  have header := outputs v
  have target : (table (v 300) (v 301) (v 302) hwidth s.val.memory).OutputReady t := by
    refine ⟨scratch,seven,RationalAccumulator.blank_of_eq (frame.tapes 37 (by decide)) ho.packing,
      ?_,?_,?_,?_,clock,?_,?_,?_⟩
    · change RationalAccumulator.Word t.val 210 (v 301)
      simpa only [header.1] using bank 210 (by simp [ids,headerIds])
    · change RationalAccumulator.Word t.val 212 (v 302)
      simpa only [header.2.1] using bank 212 (by simp [ids,headerIds])
    · change RationalAccumulator.Word t.val 213 (v 302+tableSize (v 300)*v 301)
      simpa only [header.2.2.1] using bank 213 (by simp [ids,headerIds])
    · change RationalAccumulator.Word t.val 214 (v 302+2*tableSize (v 300)*v 301)
      simpa only [header.2.2.2.1] using bank 214 (by simp [ids,headerIds])
    · simpa only [table,addressValue_bits,frame.memory] using
        memoryWords_represents s.val.memory (v 302) (v 301) (tableSize (v 300))
    · simpa only [table,addressValue_bits,frame.memory] using
        memoryWords_represents s.val.memory (v 302+tableSize (v 300)*v 301) (v 301) (tableSize (v 300))
    · simpa only [table,addressValue_bits,frame.memory] using
        memoryWords_represents s.val.memory (v 302+2*tableSize (v 300)*v 301) (v 301) (tableSize (v 300))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,source,target,bank,?_,z216,frame⟩
  · have hsize : (v 301).bits.length ≤ v 301 := by
      rw [Nat.size_eq_bits_len,Nat.size_le]
      exact Nat.lt_two_pow_self
    have hcClock : c2 ≤ 2^10*(v 301+2)^2 := by
      have hproduct := Nat.mul_le_mul_left (v 301+1)
        (show 13*(v 301).bits.length+21 ≤ 13*v 301+21 by omega)
      nlinarith only [hc2,hproduct,hsize]
    have hlarge1 : (B+2)^2 ≤ (B+H+v 301+3)^2 := Nat.pow_le_pow_left (by omega) 2
    have hlarge2 : (v 301+2)^2 ≤ (B+H+v 301+3)^2 := Nat.pow_le_pow_left (by omega) 2
    have hlarge3 : H+1 ≤ (B+H+v 301+3)^2 := by
      have hh : H+1 ≤ (H+1)^2 := by nlinarith only [Nat.zero_le H]
      exact hh.trans (Nat.pow_le_pow_left (by omega) 2)
    norm_num only [clearHeaders,List.length_cons,List.length_nil,plan] at hc0 price
    nlinarith only [hc0,price,hcClock,hlarge1,hlarge2,hlarge3]
  · intro i hi
    have h := NatAssign.values_width_bound ids plan valid (clearedValues v) B
      (cleared_width v B hv) literals i hi
    change (outputValues v i).bits.length+1 ≤ 2^14*(B+1) at h
    omega

#print axioms executes

end Maxwell.Continuum.Calibration.NeumannMachine.Allocation
