import Maxwell.Cost.SourceCircuit.HornerTerm
import Maxwell.Cost.SourceCircuit.RowSum

namespace Maxwell.Cost.SourceCircuit.FinalizeRow
open Structured
open RationalAccumulator (Blank)

def initial (next gates : List Bool) (terms : List (List Bool)) : RowSum.Data where
  next := Increment.bits next
  accumulator := next
  gates := gates ++ zeroTag
  terms := terms

def result (next gates : List Bool) (terms : List (List Bool)) : RowSum.Data :=
  RowSum.complete (initial next gates terms)

def code : Code := .seq HornerTerm.zeroCode
  (.seq RowSum.outputCode (.call (TapeOps.clear 106)))

def costBound (termCount width counterWidth : ℕ) : ℕ :=
  RowSum.costBound termCount width counterWidth + 56*width+6*counterWidth+88

theorem executes (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (next gates clock counter outputs : List Bool) (terms : List (List Bool)) (counterOrigin : ℤ)
    (s : Store) (hlen : next.length = width) (hc : clock.length = width)
    (ht : ∀ word ∈ terms, word.length = width)
    (hroom : addressValue next + 1 + terms.length < 2^width)
    (hcount : addressValue counter = terms.length)
    (hs : BankArray.Scratch s.val) (h94 : Blank s.val 94) (h96 : Blank s.val 96)
    (h99 : Blank s.val 99) (hn : BankArray.Word s.val 95 next)
    (hg : s.val.tapes 97 = BitTape.atEnd gates) (h103 : s.val.tapes 103 = BitTape.blank)
    (h104 : s.val.tapes 104 = BitTape.atEnd terms.flatten)
    (h105 : s.val.tapes 105 = BitTape.atEnd outputs)
    (h106 : s.val.tapes 106 = BitTape.shifted counter counterOrigin)
    (hclock : BankArray.Word s.val 93 clock) :
    ∃ cost t, cost ≤ costBound terms.length width counter.length ∧ Executes input tape code cost s t ∧
      RowSum.Done clock (result next gates terms) outputs t ∧
      RowSum.Valid width 0 (result next gates terms) ∧ Blank t.val 106 ∧
      t.val.tapes 103 = BitTape.blank ∧ t.val.memory = s.val.memory ∧
      Frame RowSum.outputWork s.val t.val := by
  obtain ⟨zc,z,hzc,ez,zr,zm,zf⟩ := HornerTerm.zero_executes input tape next gates clock [] s
    hs h94 h96 h99 hn hg (by simpa [BitTape.atEnd_nil] using h103) hclock
  have ready : RowSum.Ready clock (initial next gates terms) z :=
    ⟨zr.scratch,zr.blank96,zr.blank99,zr.next,zr.accumulator,zr.gates,
      (zf.tapes 104 (by omega) (by simp [accumulatorWork])).trans h104,zr.clock⟩
  have valid : RowSum.Valid width terms.length (initial next gates terms) := by
    refine ⟨?_,hlen,rfl,ht,?_⟩
    · change (Increment.bits next).length = width
      rw [increment_length next (by rw [hlen]; omega),hlen]
    · simpa [initial,Increment.bits_value] using hroom
  obtain ⟨rc,r,hrc,er,rd,rv,rm,rf,finalCounter,r106,hcounterLength⟩ := RowSum.output_executes
    input tape clock counter outputs width counterOrigin (initial next gates terms) z hc hcount
    ((zf.tapes 106 (by omega) (by simp [accumulatorWork])).trans h106)
    ((zf.tapes 105 (by omega) (by simp [accumulatorWork])).trans h105) ready valid
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 106 input tape finalCounter counterOrigin r r106
  have frame : Frame RowSum.outputWork r.val t.val := frame_transfer (WordTransfer.frame_of_copy tf) (by
    intro j hj
    have hj106 : j ≠ 106 := fun he => hj (by simp [RowSum.outputWork,RowSum.work,he])
    simp [tt,hj106])
  refine ⟨zc+(rc+(6*finalCounter.length+4)),t,?_,ez.seq (er.seq et),?_,rv,
    ⟨counterOrigin+finalCounter.length,by simp [tt]⟩,?_,tf.2.2.1.trans (rm.trans zm),
    (zf.mono (by decide)).trans (rf.trans frame)⟩
  · change rc ≤ RowSum.costBound terms.length width counter.length+17*width+14 at hrc
    rw [hlen] at hzc
    unfold costBound
    omega
  · exact ⟨scratch_of_tapes rd.scratch (by intro j hj; simp [tt,show j ≠ 106 by omega]),
      RationalAccumulator.blank_of_eq (by simp [tt]) rd.blank94,
      RationalAccumulator.blank_of_eq (by simp [tt]) rd.blank96,
      RationalAccumulator.blank_of_eq (by simp [tt]) rd.blank99,
      BankArray.word_of_eq (by simp [tt]) rd.next,by simpa [tt,result] using rd.gates,
      by simpa [tt] using rd.terms,BankArray.word_of_eq (by simp [tt]) rd.clock,
      by simpa [tt,result] using rd.outputs⟩
  · rw [tt]
    simp only [Function.update_of_ne (show (103:ℕ) ≠ 106 by omega)]
    exact (rf.tapes 103 (by omega) (by simp [RowSum.outputWork,RowSum.work])).trans
      ((zf.tapes 103 (by omega) (by simp [accumulatorWork])).trans h103)

end Maxwell.Cost.SourceCircuit.FinalizeRow
