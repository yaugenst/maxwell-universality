import Maxwell.Cost.DoublingInit.Read
import Maxwell.Cost.DoublingInit.Pack
import Maxwell.Cost.DoublingInit.Write
import Maxwell.Cost.DoublingInit.Cleanup
import Maxwell.Cost.DoublingInit.StepEncoding

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def stepCode : Code := .seq readCode (.seq packCode (.seq writeCode cleanupCode))

theorem step_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (i : Fin n) (index clock : List Bool)
    (hw : 0<layout.route.width) (hn : n≤2^layout.route.width) (hlen : index.length≤layout.route.width)
    (hi : addressValue index=i.val) (hc : clock.length=layout.route.width) (hsep : layout.Separated n)
    (s : Store) (cfg : Config layout index clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory a b i.val) :
    ∃ cost t, cost≤250000*(budget layout index+1)^2 ∧ Executes input tape stepCode cost s t ∧
      Config layout index clock t.val ∧ Workspace t.val ∧
      Represents layout t.val.memory a b (i.val+1) ∧ Frame s.val t.val ∧
      DoublingPass.MemoryFrame layout.route n s.val.memory t.val.memory := by
  obtain ⟨rc,r,hrc,er,r88,r89,rss,r7,restR,rm,cfgR,rf⟩ := read_executes input tape layout a b i index clock
    hw hn hi hc s cfg work rep.inputA rep.inputB
  obtain ⟨pc,p,hpc,ep,p37,pss,p7,pm,cfgP,pf⟩ := pack_executes input tape layout i index clock
    hw hi hlen hc r cfgR rss r7 (restR 37 (Or.inl rfl))
  have p89 := BankArray.word_of_eq (pf.2.2.2.1 89 (by omega) (by omega)) r89
  obtain ⟨wc,w,hwc,ew,wss,w7,wm,cfgW,wf⟩ := write_executes input tape layout a b i index clock
    hw hi p cfgP pss p89 p37
  obtain ⟨t,et,workT,tm,tf⟩ := cleanup_executes input tape
    (IncidenceEncoding.word layout.route.width (b i).val)
    (IncidenceEncoding.word layout.route.width (a (b i)).val)
    (IncidenceEncoding.word layout.route.width i.val) w
    (BankArray.word_of_eq ((wf.2.2.2.1 88 (by omega)).trans (pf.2.2.2.1 88 (by omega) (by omega))) r88)
    (BankArray.word_of_eq (wf.2.2.2.1 89 (by omega)) p89)
    (BankArray.word_of_eq (wf.2.2.2.1 37 (by omega)) p37)
    wss (RationalAccumulator.blank_of_eq w7 p7)
    (fun k hk hk' => RationalAccumulator.blank_of_eq
      ((wf.2.2.2.1 k (by omega)).trans (pf.2.2.2.1 k (by omega) (by omega))) (restR k (Or.inr ⟨hk,hk'⟩)))
  refine ⟨rc+(pc+(wc+(6*((IncidenceEncoding.word layout.route.width (b i).val).length+
      (IncidenceEncoding.word layout.route.width (a (b i)).val).length+
      (IncidenceEncoding.word layout.route.width i.val).length)+12))),t,?_,
    er.seq (ep.seq (ew.seq et)),cfgW.of_frame tf,workT,?_,
    rf.trans ((Frame.of_except (Or.inl rfl) pf).trans ((Frame.of_bank wf).trans tf)),?_⟩
  · simp only [IncidenceEncoding.word_length]
    have hb : layout.route.width≤budget layout index := by dsimp [budget,DoublingPass.budget]; omega
    nlinarith
  · rw [tm,wm,pm,rm]
    exact represents_step i.isLt rep hsep
  · rw [tm,wm,pm,rm]
    exact stepMemory_frame layout a b i s.val.memory

end Maxwell.Cost.DoublingInit
