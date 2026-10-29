import Maxwell.Cost.PositiveGraph.Initialize.Common
import Maxwell.Cost.PowerOfTwo

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Blank)

def eightCode : Code := .seq (PowerOfTwo.appendBit 162 false)
  (.seq (PowerOfTwo.appendBit 162 false) (.seq (PowerOfTwo.appendBit 162 false)
    (.seq (PowerOfTwo.appendBit 162 true) (.call (Rewind.program 162)))))

/-- Eight is emitted by four Boolean writes, rather than installed as an
unpriced initial memory value. -/
theorem eight_executes (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Blank s.val 162) :
    ∃ t, Executes input tape eightCode 46 s t ∧ RationalAccumulator.Word t.val 162 8 ∧
      t.val.memory=s.val.memory ∧ (∀ j, j ≠ 162 → t.val.tapes j=s.val.tapes j) ∧ Frame s.val t.val := by
  obtain ⟨origin,ho⟩ := hs
  let a := PowerOfTwo.appendState 162 false s
  let b := PowerOfTwo.appendState 162 false a
  let c := PowerOfTwo.appendState 162 false b
  let d := PowerOfTwo.appendState 162 true c
  have ha : a.val.tapes 162=BitTape.shiftedEnd [false] origin := by
    simpa using PowerOfTwo.append_word 162 false s [] origin (by simpa using ho)
  have hb : b.val.tapes 162=BitTape.shiftedEnd [false,false] origin := by
    simpa using PowerOfTwo.append_word 162 false a [false] origin ha
  have hc : c.val.tapes 162=BitTape.shiftedEnd [false,false,false] origin := by
    simpa using PowerOfTwo.append_word 162 false b [false,false] origin hb
  have hd : d.val.tapes 162=BitTape.shiftedEnd [false,false,false,true] origin := by
    simpa using PowerOfTwo.append_word 162 true c [false,false,false] origin hc
  have ea := PowerOfTwo.append_executes 162 false input tape s
  have eb := PowerOfTwo.append_executes 162 false input tape a
  have ec := PowerOfTwo.append_executes 162 false input tape b
  have ed := PowerOfTwo.append_executes 162 true input tape c
  have fd : PowerOfTwo.Frame 162 162 s d :=
    (PowerOfTwo.append_frame 162 162 false s).trans
      ((PowerOfTwo.append_frame 162 162 false a).trans
        ((PowerOfTwo.append_frame 162 162 false b).trans (PowerOfTwo.append_frame 162 162 true c)))
  have er := WordTransfer.rewind_shifted 162 origin input tape [false,false,false,true] d.val d.property hd
  let t := Store.ofState (Rewind.finishAt 162 origin d.val)
  have et : Executes input tape (.call (Rewind.program 162)) 22 d t := .call _ _ _ _ er.1 rfl
  have ft := WordTransfer.frame_rewind 162 162 162 (Or.inl rfl) origin d.val
  refine ⟨t,ea.seq (eb.seq (ec.seq (ed.seq et))),⟨origin,er.2⟩,
    ft.2.2.1.trans fd.2.2.1,fun j hj => (ft.2.2.2.2.2.1 j hj hj).trans
      (fd.2.2.2.2.2.1 j hj hj),?_⟩
  exact ⟨ft.2.1.trans fd.2.1,ft.2.2.2.1.trans fd.2.2.2.1,ft.2.2.2.2.1.trans fd.2.2.2.2.1,
    fun j _ _ _ _ hj => (ft.2.2.2.2.2.1 j hj hj).trans (fd.2.2.2.2.2.1 j hj hj),
    fun j hj h24 h25 h26 h27 h28 h29 => (ft.2.2.2.2.2.2 j h24 h25 h26 h27).trans
      (fd.2.2.2.2.2.2 j (by omega) h24 h25 h28 h29)⟩

end Maxwell.Cost.PositiveGraph.Initialize
