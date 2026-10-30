import Maxwell.Continuum.CalibrationNormalizationWidthProgram
import Maxwell.Continuum.CalibrationNormalizationLayout
import Maxwell.Continuum.CalibrationNormalizationOutput

/-! Normalization with an actually allocated destination. The program computes
the write width and all addresses before writing the exact rational mode. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def allocatedCode : Code := .seq widthCode (.seq code outputCode)
def allocatedCost (n K P B H length : ℕ) : ℕ :=
  2^100*(B+P+10)^2+2^60*(2*outputWidth n K P B+B+H+3)^2+outputCost n K P B length
def allocatedChanges : Finset ℕ := widthChanged∪changed

theorem allocated_executes {n : ℕ} (a : Buffers n) (D K P B heap H : ℕ) (count : List Bool)
    (hB : 1≤B) (hDpos : 0<D) (hD : D.bits.length≤B) (hK : K.bits.length≤B)
    (hsize : a.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (hheap : heap.bits.length≤B)
    (hafter : ∀ x∈[(data a).matrixPositiveBase,(data a).matrixNegativeBase,
      (data a).vectorPositiveBase,(data a).vectorNegativeBase],
      addressValue x+n*addressValue (data a).width≤heap)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : a.Ready count B s.val) (hden : Word s.val 126 D)
    (hb : NatAssign.Bank widthIds (widthInputs n K P B heap) s.val)
    (hheaders : WordCleanup.Bounded clearHeaders H s.val)
    (hindex : Blank s.val 140) (h216 : Blank s.val 216)
    (hfresh : ∀ i∈outputFresh, Blank s.val i) :
    ∃ cost t den, Executes input tape allocatedCode cost s t ∧
      cost≤allocatedCost n K P B H count.length ∧ 0<den ∧
      (normalizedOutput a (outputTable n K P B heap s.val.memory) D K P den).OutputReady t ∧
      CalibrationMatrix.Stored (data a) t.val ∧
      (∀ i, ((normalizedOutput a (outputTable n K P B heap s.val.memory) D K P den).get i).value=
        (arrayNormCenter a D K P)⁻¹*(((bufferChannels a).value i:ℚ)/(D^(K+1):ℕ))) ∧
      (0<arrayNormCenter a D K P → ∀ i,
        ((normalizedOutput a (outputTable n K P B heap s.val.memory) D K P den).get i).Valid) := by
  have small (m : ℕ) : m.bits.length≤m := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have hn : n.bits.length≤B := by
    rw [←hcount]
    exact (canonical_length_le count).trans hcl
  have initialWidth : ∀ i∈widthIds, (widthInputs n K P B heap i).bits.length≤B+P+8 := by
    intro i _
    have hP := small P
    have hBb := small B
    have hz : (0:ℕ).bits.length=0 := rfl
    unfold widthInputs
    split_ifs <;> omega
  obtain ⟨vi,hvi,hvl,cal,stored,indices,out,countWord,blank,h37,h108,h109⟩ := ha
  have z : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact cal.2.1.1
    · exact cal.2.1.2.1
    · exact cal.2.1.2.2.1
    · exact cal.2.1.2.2.2.1
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := width_executes n K P B heap (B+P+8) (by omega)
    initialWidth input tape s hb z
  have wv := widthValues_width n K P B heap
  have iv := widthValues_inputs n K P B heap
  have allocationBank : NatAssign.Bank inputs (widthValues n K P B heap) u.val :=
    fun i hi => b0 i ((by decide : inputs⊆widthIds) hi)
  have allocationWidth : ∀ i∈inputs, (widthValues n K P B heap i).bits.length≤outputWidth n K P B+B := by
    intro i hi
    simp only [inputs,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · rw [iv.1];omega
    · rw [wv];exact (small _).trans (Nat.le_add_right _ _)
    · rw [iv.2.1];omega
    · rw [iv.2.2];simp
  have scratch0 : BankArray.Scratch u.val :=
    ⟨z0 0 (by decide),z0 1 (by decide),z0 2 (by decide),z0 3 (by decide),
      RationalAccumulator.blank_of_eq (f0.tapes 5 (by decide)) cal.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 6 (by decide)) cal.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 8 (by decide)) cal.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 9 (by decide)) cal.2.1.2.2.2.2.2.2.2⟩
  have oldHeaders : WordCleanup.Bounded clearHeaders H u.val := by
    intro i hi
    obtain ⟨xs,hxs,word⟩ := hheaders i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i ?_) word⟩
    simp only [clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hi
    simp only [widthChanged,Finset.mem_insert,Finset.mem_singleton]
    omega
  obtain ⟨c1,v,e1,hc1,o1,_,_,f1⟩ := executes (widthValues n K P B heap) (outputWidth n K P B+B) H
    (by rw [wv];exact outputWidth_pos n K P B) allocationWidth input tape u allocationBank scratch0
    (RationalAccumulator.blank_of_eq (f0.tapes 7 (by decide)) cal.2.2)
    (RationalAccumulator.blank_of_eq (f0.tapes 37 (by decide)) h37)
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) h216) oldHeaders
  have frame : BinaryPrecision.Frame allocatedChanges s.val v.val :=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have outputReady : (outputTable n K P B heap s.val.memory).OutputReady v := by
    change (Profile.Runtime.memoryTable n (widthValues n K P B heap 571)
      (widthValues n K P B heap 572) _ u.val.memory).OutputReady v at o1
    simpa only [wv,iv.2.1,f0.memory,outputTable] using o1
  have zv : NatAssign.Scratch v.val := by
    intro i hi
    interval_cases i
    · exact outputReady.scratch.1
    · exact outputReady.scratch.2.1
    · exact outputReady.scratch.2.2.1
    · exact outputReady.scratch.2.2.2.1
  have ready := buffer_ready_frame
    (show a.Ready count B s.val from ⟨vi,hvi,hvl,cal,stored,indices,out,countWord,blank,h37,h108,h109⟩)
    frame (by intro i hi hbig;simp only [allocatedChanges,widthChanged,changed,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton];omega) zv
  have iterations : Word v.val 304 K := RationalAccumulator.word_of_eq (frame.tapes 304 (by decide))
    (by simpa [widthInputs] using hb 304 (by decide))
  have precision : Word v.val 544 P := RationalAccumulator.word_of_eq (frame.tapes 544 (by decide))
    (by simpa [widthInputs] using hb 544 (by decide))
  have fresh : ∀ i∈outputFresh, Blank v.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (frame.tapes i
      (Finset.disjoint_left.mp (by decide : Disjoint outputFresh allocatedChanges) hi)) (hfresh i hi)
  obtain ⟨c2,t,den,e2,hc2,denPos,table,st,values,valid⟩ := output_executes a
    (outputTable n K P B heap s.val.memory) D K P B count hB hDpos hD hK hsize hcount hcl
    (outputTable_metadata n K P B heap s.val.memory hheap)
    (by rw [outputTable_slot]) (outputTable_separated n K P B heap s.val.memory)
    (outputTable_separatedFrom (data a) K P B heap s.val.memory hafter)
    input tape v ready outputReady (RationalAccumulator.word_of_eq (frame.tapes 126 (by decide)) hden)
    iterations precision (RationalAccumulator.blank_of_eq (frame.tapes 140 (by decide)) hindex) fresh
  refine ⟨c0+(c1+c2),t,den,e0.seq (e1.seq e2),?_,denPos,table,st,values,valid⟩
  rw [wv] at hc1
  unfold allocatedCost
  have hcost0 : c0≤2^100*(B+P+10)^2 := by simpa only [Nat.add_assoc] using hc0
  have hcost1 : c1≤2^60*(2*outputWidth n K P B+B+H+3)^2 := by
    convert hc1 using 1
    ring
  omega

#print axioms allocated_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation
