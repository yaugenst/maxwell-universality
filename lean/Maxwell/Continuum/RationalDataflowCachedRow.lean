import Maxwell.Continuum.RationalDataflowCachedRead
import Maxwell.Continuum.RationalDataflowRowOutputFrame

/-! Fixed-stride reads from a generated output cache, including executed
index arithmetic and cleanup. Original source headers are preserved. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def cachedRowCode (stride offset target : ℕ) : Code :=
  .seq (RowIndex.code stride offset)
    (.seq (cachedReadCode 221 target) (NatAssign.code RowIndex.clearInstructions))

theorem cachedRow_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (stride offset target : ℕ)
    (ht : target∈S) (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (word : List Bool)
    (hix : stride*addressValue word+offset<n) (s : Store)
    (hs : RationalDataflow.Ready S v s) (ha : a.OutputReady s)
    (hi : BankArray.Word s.val 201 word)
    (hblank : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i) :
    ∃cost t,Executes input tape (cachedRowCode stride offset target) cost s t ∧
      cost≤rowReadCost a word (v target) stride offset ∧
      RationalDataflow.Ready S (Function.update v target (a.get ⟨stride*addressValue word+offset,hix⟩)) t ∧
      a.OutputReady t ∧ (∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i) ∧
      RowFrame target s.val t.val := by
  obtain ⟨cp,p,ep,hcp,bp,zp,fp⟩ := RowIndex.executes stride offset input tape word s hi hblank hs.2
  have pstate := RowIndex.rationalReady_frame hs fp zp
  have ptable := RowIndex.outputReady_frame ha fp zp
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
  obtain ⟨cr,r,er,hcr,br,ar,_,fr⟩ := cachedRead_executes a S 221 target (by decide) (by decide)
    ht v input tape (stride*addressValue word+offset).bits ⟨stride*addressValue word+offset,hix⟩
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
    RowIndex.outputReady_frame ar fc zt,hbt,?_⟩
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

theorem Table.Ready.cachedRow_frame {n target : ℕ} {a : Table n} {s t : Store}
    (h : a.Ready s) (f : RowFrame target s.val t.val) (hz : BankArray.Scratch t.val)
    (h7 : RationalAccumulator.Blank t.val 7) : a.Ready t := by
  have keep (i : ℕ) (hlo : 10 ≤ i) (hhi : i<1000) (hindex : i∉RowIndex.ids) := f.tapes i hlo (by
    have hp := positivePort_ge target
    have hn := negativePort_ge target
    have hd := denominatorPort_ge target
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
    omega) hindex
  refine ⟨hz,h7,BankArray.word_of_eq (keep 200 (by decide) (by decide) (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide) (by decide) (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide) (by decide) (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide) (by decide) (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide) (by decide) (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

#print axioms cachedRow_executes
end Maxwell.Continuum.RationalDataflow.PartArray
