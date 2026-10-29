import Maxwell.Cost.SourceCircuit.RecordCleanup

namespace Maxwell.Cost.SourceCircuit.TermCleanup
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq (.call (TapeReset.program 15))
  (.seq (.call (TapeReset.program 16))
    (.seq (.call (TapeOps.clear 83)) (BankArray.incrementCode 106)))

def work : Finset ℕ := {15,16,83,106}

theorem executes (input : List Bool) (tape : ℕ → Bool)
    (row column bits counter : List Bool) (origin : ℤ) (s : Store)
    (hs : BankArray.Scratch s.val) (hr : s.val.tapes 15 = BitTape.atEnd row)
    (hc : s.val.tapes 16 = BitTape.atEnd column)
    (hb : s.val.tapes 83 = BitTape.shifted bits origin)
    (hcount : BankArray.Word s.val 106 counter) :
    ∃ cost t, cost ≤ 6*(row.length+column.length+bits.length)+12*counter.length+34 ∧
      Executes input tape code cost s t ∧ t.val.tapes 15 = BitTape.blank ∧
      t.val.tapes 16 = BitTape.blank ∧
      t.val.tapes 83 = {BitTape.blank with head := origin+bits.length} ∧
      BankArray.Word t.val 106 (Increment.bits counter) ∧ BankArray.Scratch t.val ∧
      t.val.memory = s.val.memory ∧ Frame work s.val t.val := by
  obtain ⟨r,er,rt,rm,rf⟩ := RecordCleanup.reset_end 15 input tape row 0 s
    (by simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using hr)
  obtain ⟨c,ec,ct,cm,cf⟩ := RecordCleanup.reset_end 16 input tape column 0 r
    (by simpa [rt,BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using hc)
  obtain ⟨b,eb,bt,bf⟩ := WordCall.clear 83 input tape bits origin c (by simpa [ct,rt] using hb)
  have bs : BankArray.Scratch b.val := scratch_of_tapes hs (by
    intro j hj
    simp [bt,ct,rt,show j ≠ 15 by omega,show j ≠ 16 by omega,show j ≠ 83 by omega])
  obtain ⟨ic,t,hic,et,tc,ts,tm,_,tk,tf⟩ := BankArray.increment_bank 106 (by omega) input tape
    counter b (BankArray.word_of_eq (by simp [bt,ct,rt]) hcount) bs
  have frameB : Frame work c.val b.val := frame_transfer (WordTransfer.frame_of_copy bf) (by
    intro j hj
    have j83 : j ≠ 83 := fun he => hj (by simp [work,he])
    simp [bt,j83])
  refine ⟨6*row.length+6+(6*column.length+6+(6*bits.length+4+ic)),t,by omega,
    er.seq (ec.seq (eb.seq et)),?_,?_,?_,tc,ts,tm.trans (bf.2.2.1.trans (cm.trans rm)),
    (rf.mono (by simp [work])).trans ((cf.mono (by simp [work])).trans
      (frameB.trans ((frame_except tf).mono (by simp [work]))))⟩
  · simpa [bt,ct,rt,BitTape.blank] using tk 15 (by omega)
  · simpa [bt,ct,BitTape.blank] using tk 16 (by omega)
  · simpa [bt] using tk 83 (by omega)

end Maxwell.Cost.SourceCircuit.TermCleanup
