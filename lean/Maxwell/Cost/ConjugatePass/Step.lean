import Maxwell.Cost.ConjugatePass.Read
import Maxwell.Cost.ConjugatePass.Write
import Maxwell.Cost.ConjugatePass.MemoryFrame
import Maxwell.Cost.DoublingPass.Cleanup

namespace Maxwell.Cost.ConjugatePass
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

def stepCode : Code := .seq readCode (.seq writeCode DoublingPass.cleanupCode)

/-- The fixed slot kernel composes three saved lookups and clears every temporary word. -/
theorem step_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (hsep : Separated layout n) (s : Store) (cfg : Config layout index clock s.val)
    (work : Workspace s.val) (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 200000*(budget layout index+1)^2 ∧ Executes input tape stepCode cost s t ∧
      Workspace t.val ∧ Config layout index clock t.val ∧
      Represents layout t.val.memory saved (output.set j (IncidenceEncoding.word layout.width (value saved j).val)) ∧
      DoublingPass.Frame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨rc,r,hrc,er,r88,r89,r90,r91,r92,rss,r7,rm,cfgR,rf⟩ :=
    read_executes input tape layout saved output j index clock hw hn hi hc s cfg work rep
  obtain ⟨wc,w,hwc,ew,wss,w7,wm,wkeep,cfgW,wf⟩ :=
    write_executes input tape layout saved output j index clock hw hi r cfgR rss r90
      (by simpa only [rm] using rep)
  have w91 : Word w.val 91 [] := by
    obtain ⟨o,ho⟩ := r91
    exact ⟨o,by simpa only [wkeep 91 (by omega),BitTape.shifted_nil] using ho⟩
  have w92 : Word w.val 92 [] := by
    obtain ⟨o,ho⟩ := r92
    exact ⟨o,by simpa only [wkeep 92 (by omega),BitTape.shifted_nil] using ho⟩
  obtain ⟨t,et,tw,tm,tf⟩ := DoublingPass.cleanup_executes input tape
    (labelWord layout (saved.forward.get j)) (labelWord layout (saved.pairing.get (saved.forward.get j)))
    (labelWord layout (value saved j)) [] [] w
    (BankArray.word_of_eq (wkeep 88 (by omega)) r88)
    (BankArray.word_of_eq (wkeep 89 (by omega)) r89)
    (BankArray.word_of_eq (wkeep 90 (by omega)) r90) w91 w92 wss
    (RationalAccumulator.blank_of_eq w7 r7)
  refine ⟨rc+(wc+(6*((labelWord layout (saved.forward.get j)).length+
    (labelWord layout (saved.pairing.get (saved.forward.get j))).length+
    (labelWord layout (value saved j)).length+[].length+[].length)+20)),t,?_,er.seq (ew.seq et),tw,
    cfgW.of_frame tf,?_,rf.trans (wf.trans tf),?_⟩
  · simp only [IncidenceEncoding.word_length,List.length_nil]
    have hb : layout.width ≤ budget layout index := by dsimp [budget]; omega
    nlinarith
  · rw [tm,wm,rm]
    exact represents_slot rep hsep j
  · rw [tm,wm,rm]
    exact slotMemory_frame layout saved j s.val.memory

end Maxwell.Cost.ConjugatePass
