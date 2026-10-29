import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.WordReset

namespace Maxwell.Cost.SourceCircuit.RecordCleanup
open Structured

theorem reset_end (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shiftedEnd word origin) :
    ∃ t, Executes input tape (.call (TapeReset.program target)) (6*word.length+6) s t ∧
      t.val.tapes = Function.update s.val.tapes target {BitTape.blank with head := origin} ∧
      t.val.memory = s.val.memory ∧ Frame {target} s.val t.val := by
  have steps := TapeReset.shifted_steps target origin input tape word s.val s.property ht
  let t := Store.ofState (TapeReset.finishAt target origin s.val)
  refine ⟨t,.call _ s _ _ steps (by simp [TapeReset.program,TapeReset.finishAt]),rfl,rfl,?_⟩
  have ff : Frame {target} s.val (TapeReset.finishAt target origin s.val) :=
    frame_transfer (WordTransfer.frame_of_copy (TapeReset.finishAt_frame target origin s.val)) (by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      simp [TapeReset.finishAt,hj])
  exact ⟨ff.inputHead,ff.randomCursor,ff.output,ff.tapes,ff.sign,ff.control⟩

def code : Code := .seq (.call (TapeReset.program 15))
  (.seq (WordCall.resetStart 16) (.call (TapeReset.program 83)))

def work : Finset ℕ := {15,16,83}

theorem executes (input : List Bool) (tape : ℕ → Bool) (row column bits : List Bool)
    (origin : ℤ) (s : Store)
    (hr : s.val.tapes 15 = BitTape.atEnd row)
    (hc : s.val.tapes 16 = BitTape.ofList column)
    (hb : s.val.tapes 83 = BitTape.shiftedEnd bits origin) :
    ∃ t, Executes input tape code (6*row.length+11*column.length+6*bits.length+22) s t ∧
      t.val.tapes = Function.update (Function.update (Function.update s.val.tapes 15 BitTape.blank)
        16 BitTape.blank) 83 {BitTape.blank with head := origin} ∧
      t.val.memory = s.val.memory ∧ Frame work s.val t.val := by
  obtain ⟨r,er,rt,rm,rf⟩ := reset_end 15 input tape row 0 s
    (by simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using hr)
  obtain ⟨c,ec,ct,cf⟩ := WordCall.reset_start 16 input tape column 0 r
    (by simpa [rt,BitTape.shifted,BitTape.ofList] using hc)
  obtain ⟨t,et,tt,tm,tf⟩ := reset_end 83 input tape bits origin c (by simpa [ct,rt] using hb)
  have cf' : Frame work r.val c.val := frame_transfer cf (by
    intro j hj
    have hj16 : j ≠ 16 := fun he => hj (by simp [work,he])
    simp [ct,hj16])
  refine ⟨t,?_,by simpa [rt,ct,BitTape.blank] using tt,tm.trans (cf.2.2.1.trans rm),
    (rf.mono (by simp [work])).trans (cf'.trans (tf.mono (by simp [work])))⟩
  convert er.seq (ec.seq et) using 1 <;> first | rfl | omega

end Maxwell.Cost.SourceCircuit.RecordCleanup
