import Maxwell.Continuum.RationalDataflowRowFrame

/-! One fixed-stride row read, including index arithmetic, three actual
memory reads, canonicalization and cleanup of the temporary index words. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def rowReadCode (stride offset target : ℕ) : Code :=
  .seq (RowIndex.code stride offset)
    (.seq (readAtCode 221 target) (NatAssign.code RowIndex.clearInstructions))

def rowReadCost {n : ℕ} (a : Table n) (word : List Bool) (old : Parts) (stride offset : ℕ) : ℕ :=
  2^22*(word.length+stride.bits.length+offset.bits.length+5)^2+
    a.readCost (stride*addressValue word+offset).bits old+
      6*((addressValue word).bits.length+(stride*addressValue word+offset).bits.length+offset.bits.length)+34

structure RowFrame (target : ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,10 ≤ i → i∉cellPorts target → i∉RowIndex.ids → t.tapes i=s.tapes i

theorem rowRead_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (stride offset target : ℕ)
    (ht : target∈S) (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (word : List Bool)
    (hix : stride*addressValue word+offset<n) (s : Store)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃ cost t, Executes input tape (rowReadCode stride offset target) cost s t ∧
      cost≤rowReadCost a word (v target) stride offset ∧
      RationalDataflow.Ready S (Function.update v target (a.get ⟨stride*addressValue word+offset,hix⟩)) t ∧
      a.Ready t ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧ RowFrame target s.val t.val := by
  obtain ⟨cp,p,ep,hcp,bp,zp,fp⟩ := RowIndex.executes stride offset input tape word s hi hblank hs.2
  have pstate := RowIndex.rationalReady_frame hs fp zp
  have ptable := RowIndex.tableReady_frame ha fp zp
  have pi : BankArray.Word p.val 221 (stride*addressValue word+offset).bits := by
    simpa [RowIndex.values,BankArray.Word,RationalAccumulator.Word] using
      bp 221 (by simp [RowIndex.ids])
  have outside (i : ℕ) (him : i∈RowIndex.ids) : 10 ≤ i ∧ i∉cellPorts target := by
    have hp := positivePort_ge target
    have hn := negativePort_ge target
    have hd := denominatorPort_ge target
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at him
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  obtain ⟨cr,r,er,hcr,br,ar,_,fr⟩ := readAt_executes a S 221 target (by decide)
    (outside 221 (by simp [RowIndex.ids])).2 ht v input tape
    (stride*addressValue word+offset).bits ⟨stride*addressValue word+offset,hix⟩
    (addressValue_bits _) p pstate ptable pi
  have rb : NatAssign.Bank RowIndex.ids (RowIndex.values stride offset (addressValue word)) r.val := by
    intro i him
    exact RationalAccumulator.word_of_eq (fr.tapes i (outside i him).1 (outside i him).2) (bp i him)
  obtain ⟨cc,t,ec,hcc,hbt,zt,fc⟩ := RowIndex.clear_executes
    (RowIndex.values stride offset (addressValue word)) input tape r rb br.2
  have hcc' : cc≤6*((addressValue word).bits.length+
      (stride*addressValue word+offset).bits.length+offset.bits.length)+34 := by
    simpa [RowIndex.values] using hcc
  refine ⟨cp+(cr+cc),t,ep.seq (er.seq ec),?_,RowIndex.rationalReady_frame br fc zt,
    RowIndex.tableReady_frame ar fc zt,hbt,?_⟩
  · unfold rowReadCost
    omega
  · refine ⟨fc.memory.trans (fr.memory.trans fp.memory),
      fc.inputHead.trans (fr.inputHead.trans fp.inputHead),
      fc.randomCursor.trans (fr.randomCursor.trans fp.randomCursor),
      fc.output.trans (fr.output.trans fp.output),?_⟩
    intro i hge hct hid
    have hic : i∉RowIndex.changed := by
      simp only [RowIndex.changed,Finset.mem_insert,Finset.mem_singleton,not_or]
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hid
      omega
    exact (fc.tapes i hic).trans ((fr.tapes i hge hct).trans (fp.tapes i hic))

theorem rowReadCost_polynomial {n : ℕ} (a : Table n) (word : List Bool) (old : Parts)
    (stride offset W : ℕ) (hm : a.MetadataWidth W) (hw : word.length≤W) (ho : old.Width W) :
    rowReadCost a word old stride offset≤2^30*(W+stride.bits.length+offset.bits.length+5)^2 := by
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
  have hread := a.readCost_bound (W+stride.bits.length+offset.bits.length+1)
    (hm.mono hW) _ hindex old (ho.mono hW)
  have hp := Nat.pow_le_pow_left (by omega :
    word.length+stride.bits.length+offset.bits.length+5≤W+stride.bits.length+offset.bits.length+5) 2
  unfold rowReadCost
  nlinarith only [hread,hp,hindex,hr,hw,Nat.zero_le W,Nat.zero_le stride.bits.length,
    Nat.zero_le offset.bits.length]

#print axioms rowRead_executes
#print axioms rowReadCost_polynomial
end Maxwell.Continuum.RationalDataflow.PartArray
