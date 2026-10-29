import Maxwell.Cost.ChildPermutation.Common
import Maxwell.Cost.WordPenultimate

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing.Coloring.NumericSplit

def upperCode : Code := .seq (BankArray.packCanonicalCode 81 83) (WordPenultimate.code 37)

/-- Build the upper-half address by literal packing and one physical bit flip. -/
theorem upper_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (index clock childClock : List Bool) (i : Fin (2^k))
    (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.parentWidth) (hc : clock.length=layout.parentWidth)
    (s : Store) (cfg : Config layout index clock childClock s.val)
    (ss : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37) :
    ∃ cost t, cost≤110*(layout.parentWidth+1) ∧ Executes input tape upperCode cost s t ∧
      Word t.val 37 (IncidenceEncoding.word layout.parentWidth (upper i).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock childClock t.val ∧ BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨pc,p,hpc,ep,pw,ps,p7,pm,pf⟩ := BankArray.pack_canonical 81 83 (by omega) (by omega)
    input tape index clock (by omega) (by omega) s ss h7 h37 cfg.index cfg.clock
  have he : FixedWidth.bits clock.length index=IncidenceEncoding.word layout.parentWidth (lower i).val := by
    apply SourceCircuit.fixedWidth_eq
    · simp [hc]
    · rw [FixedWidth.bits_value _ _ (by omega),hi]
      rfl
  obtain ⟨xs,b,hxs,hword,hflip⟩ := HalfPair.exists_flip_word k (lower i)
  obtain ⟨origin,ho⟩ := pw
  have hpword : p.val.tapes 37=BitTape.shifted (xs++[b,false]) origin := by
    have hx : IncidenceEncoding.word (k+2) (lower i).val=xs++[b,false] := hword
    simpa only [he,hw,hx] using ho
  obtain ⟨t,et,tw,tf⟩ := WordPenultimate.executes 37 input tape xs b false origin p hpword
  have hpair : halfSwap (2^k) (lower i)=upper i := by
    apply Fin.ext
    simp [halfSwap_val,lower,upper,i.isLt]
  have fw : Word t.val 37 (IncidenceEncoding.word layout.parentWidth (upper i).val) := by
    refine ⟨origin,?_⟩
    simpa only [hflip,hpair,hw,SourceCircuit.fixedWidth,IncidenceEncoding.word] using tw
  have frame : BankArray.FrameExcept 37 s.val t.val :=
    ⟨tf.2.1.trans pf.1,tf.2.2.2.1.trans pf.2.1,tf.2.2.2.2.1.trans pf.2.2.1,
      fun j hj h37 => (tf.2.2.2.2.2.1 j h37 h37).trans (pf.2.2.2.1 j hj h37),
      fun j hj h24 h25 h26 h27 h28 h29 => (tf.2.2.2.2.2.2 j h24 h25 h26 h27).trans
        (pf.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)⟩
  refine ⟨pc+(9*(xs.length+2)+19),t,by omega,ep.seq et,fw,
    scratch_of_tapes (fun j hj => tf.2.2.2.2.2.1 j (by omega) (by omega)) ps,
    RationalAccumulator.blank_of_eq (tf.2.2.2.2.2.1 7 (by omega) (by omega)) p7,
    tf.2.2.1.trans pm.2.2.2.1,cfg.of_frame (Frame.of_except (Or.inl rfl) frame),frame⟩

end Maxwell.Cost.ChildPermutation
