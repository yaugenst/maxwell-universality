import Maxwell.Cost.HalfPair.Encoding
import Maxwell.Cost.DoublingInit.Pack
import Maxwell.Cost.WordPenultimate
import Maxwell.Cost.BankArray.Write

namespace Maxwell.Cost.HalfPair
open Structured DoublingInit
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing.Coloring.NumericSplit

def stepCode : Code := .seq (BankArray.packCanonicalCode 81 83)
  (.seq (WordPenultimate.code 37) (.seq (BankArray.writeCode 80 81 86 37) (.call (TapeOps.clear 37))))

private theorem scratch_transport {s t : BitRAMState}
    (h : ∀ i, i < 10 → t.tapes i=s.tapes i) (ss : BankArray.Scratch s) : BankArray.Scratch t := by
  rcases ss with ⟨s0,s1,s2,s3,s5,s6,s8,s9⟩
  exact ⟨RationalAccumulator.blank_of_eq (h 0 (by omega)) s0,
    RationalAccumulator.blank_of_eq (h 1 (by omega)) s1,
    RationalAccumulator.blank_of_eq (h 2 (by omega)) s2,
    RationalAccumulator.blank_of_eq (h 3 (by omega)) s3,
    RationalAccumulator.blank_of_eq (h 5 (by omega)) s5,
    RationalAccumulator.blank_of_eq (h 6 (by omega)) s6,
    RationalAccumulator.blank_of_eq (h 8 (by omega)) s8,
    RationalAccumulator.blank_of_eq (h 9 (by omega)) s9⟩

private theorem transfer_frame {s t : BitRAMState} (h : WordTransfer.Frame 37 37 s t) :
    DoublingInit.Frame s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i _ hp => h.2.2.2.2.2.1 i (by intro he; exact hp (Or.inl he)) (by intro he; exact hp (Or.inl he)),
    fun i _ h24 h25 h26 h27 _ _ => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

/-- Pack the current index, flip its half bit, and emit one exact pairing
entry through the actual indexed bit writer. -/
theorem step_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : DoublingInit.Layout) (output : Vector (List Bool) (2*(2^k)))
    (i : Fin (2*(2^k))) (index clock : List Bool)
    (hwidth : layout.route.width=k+2) (hlen : index.length ≤ layout.route.width)
    (hi : addressValue index=i.val) (hc : clock.length=layout.route.width)
    (s : Store) (cfg : DoublingInit.Config layout index clock s.val)
    (work : DoublingInit.Workspace s.val) (rep : Represents layout s.val.memory output) :
    ∃ cost t, cost ≤ 100000*(DoublingInit.budget layout index+1)^2 ∧ Executes input tape stepCode cost s t ∧
      DoublingInit.Config layout index clock t.val ∧ DoublingInit.Workspace t.val ∧
      Represents layout t.val.memory (output.set i ((array k).get i)) ∧
      DoublingInit.Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨pc,p,hpc,ep,p37,pss,p7,pm,cfgP,pf⟩ := DoublingInit.pack_executes input tape layout i index clock
    (by omega) hi hlen hc s cfg work.1.1 work.1.2.1 work.2
  obtain ⟨xs,b,hxs,hword,hflip⟩ := exists_flip_word k i
  obtain ⟨po,hp37⟩ := p37
  have px : p.val.tapes 37=BitTape.shifted (xs++[b,false]) po := by
    have he : IncidenceEncoding.word layout.route.width i.val=xs++[b,false] := by
      simpa only [hwidth,IncidenceEncoding.word,SourceCircuit.fixedWidth] using hword
    simpa only [he] using hp37
  obtain ⟨c,ec,c37,cf⟩ := WordPenultimate.executes 37 input tape xs b false po p px
  have cw : Word c.val 37 ((array k).get i) := by
    refine ⟨po,?_⟩
    simpa [hflip,array,Vector.get,Fin.cast] using c37
  have css := scratch_transport (fun j hj => cf.2.2.2.2.2.1 j (by omega) (by omega)) pss
  have cfgC := cfgP.of_frame (transfer_frame cf)
  have repC : Represents layout c.val.memory output := by simpa only [cf.2.2.1,pm] using rep
  have payloadLength : ((array k).get i).length=layout.route.width := by simp [array,Vector.get,Fin.cast,hwidth]
  obtain ⟨wc,w,hwc,ew,wm,repW,wss,w7,wf⟩ := BankArray.write_bank 80 81 86 37
    (by omega) (by omega) (by omega) (by omega) input tape layout.route.width.bits index
    layout.route.newMinimum.bits ((array k).get i) output i (RationalAccumulator.bits_nonempty (by omega)) hi
    (by simpa only [addressValue_bits] using payloadLength) c css cfgC.route.width cfgC.route.index
    cfgC.route.newMinimum cw (by simpa only [addressValue_bits] using repC)
  obtain ⟨wo,hw37⟩ := cw
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 37 input tape ((array k).get i) wo w
    ((wf.2.2.2.1 37 (by omega)).trans hw37)
  have keepT (j : ℕ) (hj : j≠37) : t.val.tapes j=w.val.tapes j := tf.2.2.2.2.2.1 j hj hj
  have cfgT := (cfgC.of_frame (DoublingInit.Frame.of_bank wf)).of_frame
    (DoublingInit.Frame.of_clear (Or.inl rfl) tf)
  have tw : DoublingInit.Workspace t.val := by
    refine ⟨⟨scratch_transport (fun j hj => keepT j (by omega)) wss,?_,?_⟩,
      ⟨wo+((array k).get i).length,by simp [tt]⟩⟩
    · exact RationalAccumulator.blank_of_eq ((keepT 7 (by omega)).trans (w7.trans
        (cf.2.2.2.2.2.1 7 (by omega) (by omega)))) p7
    · intro j hj
      have high : 10 ≤ j := by dsimp [DoublingPass.Private] at hj; omega
      have h37 : j≠37 := by dsimp [DoublingPass.Private] at hj; omega
      exact RationalAccumulator.blank_of_eq ((keepT j h37).trans ((wf.2.2.2.1 j (Or.inr high)).trans
        ((cf.2.2.2.2.2.1 j h37 h37).trans (pf.2.2.2.1 j (Or.inr high) h37)))) (work.1.2.2 j hj)
  refine ⟨pc+(9*(xs.length+2)+19+(wc+(6*((array k).get i).length+4))),t,?_,
    ep.seq (ec.seq (ew.seq et)),cfgT,tw,?_,
    (DoublingInit.Frame.of_except (Or.inl rfl) pf).trans ((transfer_frame cf).trans
      ((DoublingInit.Frame.of_bank wf).trans (DoublingInit.Frame.of_clear (Or.inl rfl) tf))),?_⟩
  · have hcap : BankArray.costCap layout.route.width.bits index layout.route.newMinimum.bits ((array k).get i) ≤
        30000*(DoublingInit.budget layout index+1)^2 := by
      apply DoublingInit.array_cost_bound
      · dsimp [DoublingInit.budget,DoublingPass.budget]; omega
      · dsimp [DoublingInit.budget,DoublingPass.budget]; omega
      · omega
    have hbudget : layout.route.width ≤ DoublingInit.budget layout index := by
      dsimp [DoublingInit.budget,DoublingPass.budget]; omega
    nlinarith
  · simpa only [tf.2.2.1,addressValue_bits] using repW
  · rw [tf.2.2.1,wm]
    simp only [addressValue_bits,cf.2.2.1,pm]
    exact slotMemory_frame layout k i hwidth s.val.memory

end Maxwell.Cost.HalfPair
