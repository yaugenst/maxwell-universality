import Maxwell.Cost.ColorPass.MemoryFrame
import Maxwell.Cost.ColorPass.Compare
import Maxwell.Cost.ColorPass.Write
import Maxwell.Cost.DoublingPass.Cleanup

namespace Maxwell.Cost.ColorPass
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

def stepCode : Code := .seq readCode (.seq compareCode (.seq writeCode DoublingPass.cleanupCode))

/-- Three saved-array reads, one numeric comparison, and a one-bit write,
with all private workspace reclaimed. -/
theorem step_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : State n) (output : Vector Bool n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width) (hone : layout.newMinimum = 1)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (hsep : Separated layout n) (s : Store) (cfg : Config layout index clock s.val)
    (work : Workspace s.val) (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 200000 * (budget layout index + 1)^2 ∧
      Executes input tape stepCode cost s t ∧ Workspace t.val ∧ Config layout index clock t.val ∧
      Represents layout t.val.memory saved (output.set j (bit saved j)) ∧ DoublingPass.Frame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨rcost,r,hrc,er,r88,r89,r90,r91,r92,rss,r7,rm,cfgR,rf⟩ :=
    read_executes input tape layout saved output j index clock hw hn hi hc s cfg work rep
  obtain ⟨c,ec,c91,css,cm,ck,cf⟩ := compare_executes input tape layout saved j hn r r89 r90 r91 rss
  have repC : Represents layout c.val.memory saved output := by simpa [cm,rm] using rep
  obtain ⟨wcost,w,hwc,ew,wss,w7,wm,wkeep,cfgW,wf⟩ :=
    write_executes input tape layout saved output j index clock hone hi c (cfgR.of_frame cf) css c91 repC
  have keep (i : ℕ) (hi : 10 ≤ i) (h91 : i ≠ 91) : w.val.tapes i = r.val.tapes i :=
    (wkeep i (Or.inr hi)).trans (ck i (by omega) h91)
  have w92 : Word w.val 92 [] := by
    obtain ⟨o,ho⟩ := r92
    exact ⟨o,by simpa [keep 92 (by omega) (by omega),BitTape.shifted_nil] using ho⟩
  obtain ⟨t,et,tw,tm,tf⟩ := DoublingPass.cleanup_executes input tape
    (labelWord layout (saved.jump.get j)) (labelWord layout (saved.minimum.get j))
    (labelWord layout (saved.minimum.get (saved.jump.get j))) [bit saved j] [] w
    (BankArray.word_of_eq (keep 88 (by omega) (by omega)) r88)
    (BankArray.word_of_eq (keep 89 (by omega) (by omega)) r89)
    (BankArray.word_of_eq (keep 90 (by omega) (by omega)) r90)
    (BankArray.word_of_eq (wkeep 91 (by omega)) c91) w92 wss
    (RationalAccumulator.blank_of_eq (w7.trans (ck 7 (by omega) (by omega))) r7)
  refine ⟨rcost + (80*layout.width+76 + (wcost +
    (6*((labelWord layout (saved.jump.get j)).length + (labelWord layout (saved.minimum.get j)).length +
      (labelWord layout (saved.minimum.get (saved.jump.get j))).length + [bit saved j].length + [].length)+20))),
    t,?_,er.seq (ec.seq (ew.seq et)),tw,cfgW.of_frame tf,?_,rf.trans (cf.trans (wf.trans tf)), ?_⟩
  · simp only [IncidenceEncoding.word_length,List.length_singleton,List.length_nil]
    have hb : layout.width ≤ budget layout index := by dsimp [budget]; omega
    nlinarith
  · rw [tm,wm]
    exact represents_slot repC hsep j

  · rw [tm,wm]
    simpa only [cm,rm] using slotMemory_frame layout saved j c.val.memory

end Maxwell.Cost.ColorPass
