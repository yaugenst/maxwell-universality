import Maxwell.Cost.ColorAssemble.Read
import Maxwell.Cost.ColorAssemble.Write
import Maxwell.Cost.ColorAssemble.Cleanup

namespace Maxwell.Cost.ColorAssemble
open Structured
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Frame Workspace budget)

def stepCode : Code := .seq readCode (.seq writeCode cleanupCode)

/-- One complete label assembly iteration restores all transient tapes. -/
theorem step_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (out : Output k) (index clock childClock : List Bool)
    (i : Fin (2*(2^k))) (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.parentWidth) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : Separated layout k)
    (s : Store) (cfg : Config layout index clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory data out) :
    ∃ cost t, cost≤150000*(budget layout index+1)^2 ∧ Executes input tape stepCode cost s t ∧
      Config layout index clock childClock t.val ∧ Workspace t.val ∧
      t.val.memory=stepMemory layout data i s.val.memory ∧
      Represents layout t.val.memory data (stepOutput layout data i out) ∧
      Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨rc,r,hrc,er,r88,r37,r90,rss,r7,r89,r91,r92,rm,rcfg,rf⟩ :=
    read_executes k input tape layout data out index clock childClock i hw hi hlen hc hcc s cfg work rep
  obtain ⟨wc,w,hwc,ew,wm,wr,wcfg,wss,w7,wf,wmem⟩ := write_executes input tape layout data out i
    index clock childClock (by omega) hi hs r rcfg rss r90 (by simpa only [rm] using rep)
  have word {j : ℕ} {bits : List Bool} (hj : j=4 ∨ 10≤j) (h : BankArray.Word r.val j bits) : BankArray.Word w.val j bits :=
    BankArray.word_of_eq (wf.2.2.2.1 j hj) h
  have blank {j : ℕ} (hj : j=4 ∨ 10≤j) (h : Blank r.val j) : Blank w.val j :=
    RationalAccumulator.blank_of_eq (wf.2.2.2.1 j hj) h
  obtain ⟨t,et,tw,tm,tf⟩ := cleanup_executes input tape [data.colors.get i]
    (IncidenceEncoding.word layout.parentWidth (data.value i).val)
    (IncidenceEncoding.word layout.childWidth (childIndex k i).val) w
    (word (by omega) r88) (word (by omega) r90) (word (by omega) r37)
    (blank (by omega) r89) (blank (by omega) r91) (blank (by omega) r92) wss
    (RationalAccumulator.blank_of_eq w7 r7)
  refine ⟨rc+(wc+(6*([data.colors.get i].length+
    (IncidenceEncoding.word layout.parentWidth (data.value i).val).length+
    (IncidenceEncoding.word layout.childWidth (childIndex k i).val).length)+24)),t,?_,
    er.seq (ew.seq et),wcfg.of_frame tf,tw,by rw [tm,wm,rm],by simpa only [tm] using wr,
    rf.trans ((Frame.of_bank wf).trans tf),by simpa only [tm,rm] using wmem⟩
  have hp : layout.parentWidth≤budget layout index := by dsimp [budget]; omega
  have hchild : layout.childWidth≤budget layout index := by dsimp [budget]; omega
  simp only [List.length_cons,List.length_nil,IncidenceEncoding.word_length]
  nlinarith

end Maxwell.Cost.ColorAssemble
