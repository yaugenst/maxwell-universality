import Maxwell.Cost.DoublingPass.Read
import Maxwell.Cost.DoublingPass.Write
import Maxwell.Cost.DoublingPass.Cleanup
import Maxwell.Cost.DoublingPass.MemoryFrame

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def stepCode : Code := .seq readCode
  (.seq (BankArray.minimumCode 90 91 92) (.seq writeCode cleanupCode))

/-- One actual fixed Boolean program computes a cached pointer-doubling
slot from four saved-array reads and two output writes. The minimum uses
bitwise subtraction and a charged branch, not host ordering. -/
theorem step_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2 ^ layout.width)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (hsep : layout.Separated n) (s : Store) (cfg : Config layout index clock s.val)
    (work : Workspace s.val) (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 300000 * (budget layout index + 1)^2 ∧
      Executes input tape stepCode cost s t ∧ Workspace t.val ∧ Config layout index clock t.val ∧
      Represents layout t.val.memory saved (slot saved output j) ∧ Frame s.val t.val ∧ MemoryFrame layout n s.val.memory t.val.memory := by
  obtain ⟨rcost, r, hrc, er, r88, r89, r90, r91, r92, rss, r7, rm, cfgR, rf⟩ :=
    read_executes input tape layout saved output j index clock hw hn hi hc s cfg work rep
  obtain ⟨m, em, m92, mss, mm, mkeep, mf⟩ := BankArray.minimum_bank 90 91 92
    (by omega) (by omega) (by omega) (by omega) (by omega) input tape
    (labelWord layout (saved.minimum.get j)) (labelWord layout (saved.minimum.get (saved.jump.get j)))
    (by simp) r r90 r91 r92 rss
  have m92' : Word m.val 92 (labelWord layout
      (min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j)))) := by
    have hm := BankArray.chooseMinimum_word layout.width (saved.minimum.get j).val
      (saved.minimum.get (saved.jump.get j)).val
      (lt_of_lt_of_le (saved.minimum.get j).isLt hn)
      (lt_of_lt_of_le (saved.minimum.get (saved.jump.get j)).isLt hn)
    simpa only [hm, labelWord, Fin.val_min] using m92
  have mf' : Frame r.val m.val := Frame.of_except (by simp [Private]) mf
  have m89 : Word m.val 89 (labelWord layout (saved.jump.get (saved.jump.get j))) :=
    BankArray.word_of_eq (mkeep 89 (by omega) (by omega)) r89
  have repM : Represents layout m.val.memory saved output := by simpa [mm, rm] using rep
  obtain ⟨wcost, w, hwc, ew, wss, w7, wm, wkeep, cfgW, wf⟩ :=
    write_executes input tape layout saved output j index clock hw hi hsep m (cfgR.of_frame mf') mss m89 m92' repM
  obtain ⟨t, et, tw, tm, tf⟩ := cleanup_executes input tape
    (labelWord layout (saved.jump.get j)) (labelWord layout (saved.jump.get (saved.jump.get j)))
    (labelWord layout (saved.minimum.get j)) (labelWord layout (saved.minimum.get (saved.jump.get j)))
    (labelWord layout (min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j)))) w
    (BankArray.word_of_eq ((wkeep 88 (by omega)).trans (mkeep 88 (by omega) (by omega))) r88)
    (BankArray.word_of_eq (wkeep 89 (by omega)) m89)
    (BankArray.word_of_eq ((wkeep 90 (by omega)).trans (mkeep 90 (by omega) (by omega))) r90)
    (BankArray.word_of_eq ((wkeep 91 (by omega)).trans (mkeep 91 (by omega) (by omega))) r91)
    (BankArray.word_of_eq (wkeep 92 (by omega)) m92') wss
    (RationalAccumulator.blank_of_eq (w7.trans (mkeep 7 (by omega) (by omega))) r7)
  refine ⟨rcost + (95 * (labelWord layout (saved.minimum.get j)).length + 92 +
      (wcost + (6 * ((labelWord layout (saved.jump.get j)).length +
        (labelWord layout (saved.jump.get (saved.jump.get j))).length +
        (labelWord layout (saved.minimum.get j)).length +
        (labelWord layout (saved.minimum.get (saved.jump.get j))).length +
        (labelWord layout (min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j)))).length) + 20))),
    t, ?_, er.seq (em.seq (ew.seq et)), tw, cfgW.of_frame tf, ?_, rf.trans (mf'.trans (wf.trans tf)),?_⟩
  · simp only [IncidenceEncoding.word_length]
    have hb : layout.width ≤ budget layout index := by dsimp [budget]; omega
    nlinarith
  · rw [tm, wm]
    exact represents_slot repM hsep j
  · rw [tm,wm,mm,rm]
    exact slotMemory_frame layout saved j s.val.memory

end Maxwell.Cost.DoublingPass
