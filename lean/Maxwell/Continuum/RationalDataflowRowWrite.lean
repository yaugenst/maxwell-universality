import Maxwell.Continuum.RationalDataflowArrayIndexWrite
import Maxwell.Continuum.RationalDataflowRowOutputFrame
import Maxwell.Continuum.RationalDataflowArrayOutputCost

/-! A complete fixed-stride output write, with charged index preparation,
three channel writes, and cleanup. The source table is preserved. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def rowWriteCode (stride offset entry : ℕ) : Code :=
  .seq (RowIndex.code stride offset)
    (.seq (writeAtCode 221 entry) (NatAssign.code RowIndex.clearInstructions))

def rowWriteCost {n : ℕ} (a : Table n) (word : List Bool) (x : Parts) (stride offset : ℕ) : ℕ :=
  2^22*(word.length+stride.bits.length+offset.bits.length+5)^2+
    a.writeCost (stride*addressValue word+offset).bits x+
      6*((addressValue word).bits.length+(stride*addressValue word+offset).bits.length+offset.bits.length)+34

structure RowWriteFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,10 ≤ i → i≠37 → i∉RowIndex.ids → t.tapes i=s.tapes i

theorem rowWrite_executes {n m : ℕ} (a : Table n) (b : Table m) (S : Finset ℕ)
    (stride offset entry : ℕ) (he : entry∈S) (v : ℕ→Parts)
    (hpositive : 0<addressValue b.width) (hfit : (v entry).Width (addressValue b.width))
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool)
    (hix : stride*addressValue word+offset<m) (s : Store)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape (rowWriteCode stride offset entry) cost s t ∧
      cost≤rowWriteCost b word (v entry) stride offset ∧
      RationalDataflow.Ready S v t ∧ a.Ready t ∧
      (b.set ⟨stride*addressValue word+offset,hix⟩ (v entry)).OutputReady t ∧
      (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      t.val.memory=b.writeMemory ⟨stride*addressValue word+offset,hix⟩ (v entry) s.val.memory ∧
      RowWriteFrame s.val t.val := by
  obtain ⟨cp,p,ep,hcp,bp,zp,fp⟩ := RowIndex.executes stride offset input tape word s hi hblank hs.2
  have pstate := RowIndex.rationalReady_frame hs fp zp
  have ptable := RowIndex.tableReady_frame ha fp zp
  have poutput := RowIndex.outputReady_frame hb fp zp
  have pi : BankArray.Word p.val 221 (stride*addressValue word+offset).bits := by
    simpa [RowIndex.values,BankArray.Word,RationalAccumulator.Word] using
      bp 221 (by simp [RowIndex.ids])
  obtain ⟨cw,r,ew,hcw,br,bor,mr,fr⟩ := writeAt_executes b S 221 (by decide) entry he v
    ⟨stride*addressValue word+offset,hix⟩ hpositive hfit hsep input tape
    (stride*addressValue word+offset).bits (addressValue_bits _) p pstate poutput pi
  have ar := ptable.write_output_frame hdisjoint ⟨stride*addressValue word+offset,hix⟩
    (v entry) mr fr bor.scratch bor.seven
  have rb : NatAssign.Bank RowIndex.ids (RowIndex.values stride offset (addressValue word)) r.val := by
    intro i him
    have ih : 100 ≤ i := by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at him
      omega
    exact RationalAccumulator.word_of_eq
      (fr.2.2.2.1 i (Or.inr (by omega)) (by omega)) (bp i him)
  obtain ⟨cc,t,ec,hcc,hbt,zt,fc⟩ := RowIndex.clear_executes
    (RowIndex.values stride offset (addressValue word)) input tape r rb br.2
  have hcc' : cc≤6*((addressValue word).bits.length+
      (stride*addressValue word+offset).bits.length+offset.bits.length)+34 := by
    simpa [RowIndex.values] using hcc
  change cw≤b.writeCost (stride*addressValue word+offset).bits (v entry) at hcw
  refine ⟨cp+(cw+cc),t,ep.seq (ew.seq ec),?_,RowIndex.rationalReady_frame br fc zt,
    RowIndex.tableReady_frame ar fc zt,RowIndex.outputReady_frame bor fc zt,hbt,?_,?_⟩
  · unfold rowWriteCost
    omega
  · rw [fc.memory,mr,fp.memory]
  · refine ⟨fc.inputHead.trans (fr.1.trans fp.inputHead),
      fc.randomCursor.trans (fr.2.1.trans fp.randomCursor),
      fc.output.trans (fr.2.2.1.trans fp.output),?_⟩
    intro i hge h37 hid
    have hic : i∉RowIndex.changed := by
      simp only [RowIndex.changed,Finset.mem_insert,Finset.mem_singleton,not_or]
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hid
      omega
    exact (fc.tapes i hic).trans ((fr.2.2.2.1 i (Or.inr hge) h37).trans (fp.tapes i hic))

theorem rowWriteCost_polynomial {n : ℕ} (a : Table n) (word : List Bool) (x : Parts)
    (stride offset W : ℕ) (hm : a.MetadataWidth W) (hw : word.length≤W) :
    rowWriteCost a word x stride offset≤2^30*(W+stride.bits.length+offset.bits.length+5)^2 := by
  have hr : (addressValue word).bits.length≤word.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length word)
  have hmul := RationalAccumulator.bits_mul_le stride (addressValue word)
  have hadd := RationalAccumulator.bits_add_le (stride*addressValue word) offset
  have hindex : (stride*addressValue word+offset).bits.length≤W+stride.bits.length+offset.bits.length+1 := by
    have hh : max (stride*addressValue word).bits.length offset.bits.length≤
        W+stride.bits.length+offset.bits.length := by apply max_le <;> omega
    omega
  have hW : W≤W+stride.bits.length+offset.bits.length+1 := by omega
  have hwrite := a.writeCost_bound (W+stride.bits.length+offset.bits.length+1)
    (hm.mono hW) _ hindex x
  have hp := Nat.pow_le_pow_left (by omega :
    word.length+stride.bits.length+offset.bits.length+5≤W+stride.bits.length+offset.bits.length+5) 2
  unfold rowWriteCost
  nlinarith only [hwrite,hp,hindex,hr,hw,Nat.zero_le W,Nat.zero_le stride.bits.length,
    Nat.zero_le offset.bits.length]

#print axioms rowWrite_executes
#print axioms rowWriteCost_polynomial
end Maxwell.Continuum.RationalDataflow.PartArray
