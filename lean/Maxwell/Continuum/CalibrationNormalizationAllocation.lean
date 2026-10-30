import Maxwell.Continuum.CalibrationNormalizationAllocationPlan

/-! Executed destination allocation for normalization, including all metadata
writes and construction of the runtime width clock. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code : Code := .seq (WordCleanup.code clearHeaders)
  (.seq (NatAssign.code plan) (WidthClock.code 571 216 215))

theorem executes (v : ℕ → ℕ) (B H : ℕ) (hw : 0<v 571)
    (hv : ∀ i∈inputs, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank inputs v s.val) (hz : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (h37 : Blank s.val 37) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded clearHeaders H s.val) :
    ∃ cost t, Executes input tape code cost s t ∧
      cost≤2^60*(B+H+v 571+3)^2 ∧
      (Profile.Runtime.memoryTable (v 570) (v 571) (v 572) hw s.val.memory).OutputReady t ∧
      NatAssign.Bank ids (outputValues v) t.val ∧ Blank t.val 216 ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u0,e0,hc0,z0,f0⟩ := WordCleanup.executes clearHeaders H input tape s hheaders
  have bank0 : NatAssign.Bank ids (clearedValues v) u0.val := by
    intro i hi
    by_cases hh : i∈headerIds
    · rw [clearedValues,ite_eq_left hh,RationalAccumulator.zero_word_iff_blank]
      apply z0
      simp only [headerIds,Finset.mem_insert,Finset.mem_singleton] at hh
      simp only [clearHeaders,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    · have hin := (Finset.mem_union.mp hi).resolve_right hh
      rw [clearedValues,ite_eq_right hh]
      apply RationalAccumulator.word_of_eq (f0.tapes i _) (hb i hin)
      simp only [inputs,Finset.mem_insert,Finset.mem_singleton] at hin
      simp only [List.mem_toFinset,clearHeaders,List.mem_cons,List.not_mem_nil,or_false]
      omega
  have scratch0 : NatAssign.Scratch u0.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i (by
      simp only [List.mem_toFinset,clearHeaders,List.mem_cons,List.not_mem_nil,or_false]; omega))
    interval_cases i
    · exact hz.1
    · exact hz.2.1
    · exact hz.2.2.1
    · exact hz.2.2.2.1
  obtain ⟨c1,u1,e1,hc1,bank1,z1,f1⟩ := NatAssign.executes ids ids_ge plan valid (clearedValues v)
    input tape u0 bank0 scratch0
  have literals : ∀ ins∈plan, ins.literalWidth≤B := by simp [plan,NatAssign.Instruction.literalWidth]
  have price := hc1.trans (NatAssign.price_bound ids plan valid (clearedValues v) B
    (cleared_width v B hv) literals)
  have widthWord : Word u1.val 571 (v 571) := by
    have h := bank1 571 (by simp [ids,inputs])
    change Word u1.val 571 (outputValues v 571) at h
    simpa only [(outputs v).2.2.2.2.2.1] using h
  have clock0 : Blank u1.val 215 := RationalAccumulator.blank_of_eq (f1.tapes 215 (by
    simp [NatAssign.changes,plan,NatAssign.Instruction.target])) (z0 215 (by simp [clearHeaders]))
  have temp0 : Blank u1.val 216 := RationalAccumulator.blank_of_eq
    ((f1.tapes 216 (by simp [NatAssign.changes,plan,NatAssign.Instruction.target])).trans
      (f0.tapes 216 (by simp [clearHeaders]))) h216
  obtain ⟨c2,t,e2,hc2,_,z216,clock,f2⟩ := WidthClock.executes 571 216 215
    (by decide) (by decide) (by decide) input tape (v 571).bits u1 widthWord temp0 clock0
  rw [addressValue_bits] at hc2 clock
  have frame : BinaryPrecision.Frame changed s.val t.val :=
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))
  have scratch : BankArray.Scratch t.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq (f2.tapes 0 (by decide)) (z1 0 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 1 (by decide)) (z1 1 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 2 (by decide)) (z1 2 (by decide))
    · exact RationalAccumulator.blank_of_eq (f2.tapes 3 (by decide)) (z1 3 (by decide))
    · exact RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) hz.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) hz.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) hz.2.2.2.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) hz.2.2.2.2.2.2.2
  have bank : NatAssign.Bank ids (outputValues v) t.val := by
    intro i hi
    have hn : i≠216 ∧ i≠215 := by
      simp only [ids,inputs,headerIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.word_of_eq (f2.tapes i (by simp [hn.1,hn.2])) (bank1 i hi)
  have header := outputs v
  have target : (Profile.Runtime.memoryTable (v 570) (v 571) (v 572) hw s.val.memory).OutputReady t := by
    have htable := Profile.Runtime.memoryTable_outputReady (v 570) (v 571) (v 572) hw t scratch
      (RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) h7)
      (RationalAccumulator.blank_of_eq (frame.tapes 37 (by decide)) h37)
      (by simpa only [header.1] using bank 210 (by simp [ids,headerIds]))
      (by simpa only [header.2.1] using bank 212 (by simp [ids,headerIds]))
      (by simpa only [header.2.2.1] using bank 213 (by simp [ids,headerIds]))
      (by simpa only [header.2.2.2.1] using bank 214 (by simp [ids,headerIds])) clock
    simpa only [frame.memory] using htable
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,target,bank,z216,frame⟩
  have hsize : (v 571).bits.length≤v 571 := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have hcClock : c2≤2^10*(v 571+2)^2 := by
    have hproduct := Nat.mul_le_mul_left (v 571+1)
      (show 13*(v 571).bits.length+21≤13*v 571+21 by omega)
    nlinarith only [hc2,hproduct,hsize]
  have hlarge1 : (B+2)^2≤(B+H+v 571+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlarge2 : (v 571+2)^2≤(B+H+v 571+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlarge3 : H+1≤(B+H+v 571+3)^2 := by
    have hh : H+1≤(H+1)^2 := by nlinarith only [Nat.zero_le H]
    exact hh.trans (Nat.pow_le_pow_left (by omega) 2)
  norm_num only [clearHeaders,List.length_cons,List.length_nil,plan] at hc0 price
  nlinarith only [hc0,price,hcClock,hlarge1,hlarge2,hlarge3]

#print axioms executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation
