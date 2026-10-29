import Maxwell.Cost.ChildPermutation.Common
import Maxwell.Cost.WordLift

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Frame budget)

def indexCode : Code := .seq (BankArray.packCanonicalCode 81 83) (WordReduceHalf.code 37)

/-- The child address is formed by packing the actual loop counter and
physically removing its top binary coordinate. -/
theorem index_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (index clock childClock : List Bool) (i : Fin (2*(2^k)))
    (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.parentWidth) (hc : clock.length=layout.parentWidth)
    (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37) :
    ∃ cost t, cost≤110*(layout.parentWidth+1) ∧ Executes input tape indexCode cost s t ∧
      Word t.val 37 (IncidenceEncoding.word layout.childWidth (i.val%2^k)) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock childClock t.val ∧ BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨pc,p,hpc,ep,pw,ps,p7,pm,pf⟩ := BankArray.pack_canonical 81 83 (by omega) (by omega)
    input tape index clock (by omega) (by omega) s ss h7 h37 cfg.index cfg.clock
  have he : FixedWidth.bits clock.length index=IncidenceEncoding.word (k+2) i.val := by
    apply SourceCircuit.fixedWidth_eq
    · simp [hc,hw]
    · rw [FixedWidth.bits_value _ _ (by omega),hi]
  obtain ⟨t,et,tw,tf⟩ := ChildPermutation.reduce_executes 37 k i input tape p (by simpa only [he] using pw)
  have frame : BankArray.FrameExcept 37 s.val t.val :=
    ⟨tf.2.1.trans pf.1,tf.2.2.2.1.trans pf.2.1,tf.2.2.2.2.1.trans pf.2.2.1,
      fun j hj h37 => (tf.2.2.2.2.2.1 j h37 h37).trans (pf.2.2.2.1 j hj h37),
      fun j hj h24 h25 h26 h27 h28 h29 => (tf.2.2.2.2.2.2 j h24 h25 h26 h27).trans
        (pf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)⟩
  refine ⟨pc+(9*k+31),t,by omega,ep.seq et,?_,
    ChildPermutation.scratch_of_tapes (fun j hj => tf.2.2.2.2.2.1 j (by omega) (by omega)) ps,
    RationalAccumulator.blank_of_eq (tf.2.2.2.2.2.1 7 (by omega) (by omega)) p7,
    tf.2.2.1.trans pm.2.2.2.1,cfg.of_frame (Frame.of_except (Or.inl rfl) frame),frame⟩
  simpa only [Layout.childWidth,hw,show k+2-1=k+1 by omega] using tw

end Maxwell.Cost.ColorAssemble
