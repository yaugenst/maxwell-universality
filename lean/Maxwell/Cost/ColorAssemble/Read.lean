import Maxwell.Cost.ColorAssemble.Encoding
import Maxwell.Cost.ColorAssemble.ReadColor
import Maxwell.Cost.ColorAssemble.ReadChild

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Frame Private Workspace budget)

def readCode : Code := .seq readColorCode (.seq indexCode (.seq readChildCode (WordLift.code 90 30)))

/-- A routing-label slot is assembled from the stored color and exactly one
stored child label. Every address computation and word manipulation executes. -/
theorem read_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (out : Output k) (index clock childClock : List Bool)
    (i : Fin (2*(2^k))) (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.parentWidth) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (s : Store)
    (cfg : Config layout index clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory data out) :
    ∃ cost t, cost≤100000*(budget layout index+1)^2 ∧ Executes input tape readCode cost s t ∧
      Word t.val 88 [data.colors.get i] ∧
      Word t.val 37 (IncidenceEncoding.word layout.childWidth (childIndex k i).val) ∧
      Word t.val 90 (IncidenceEncoding.word layout.parentWidth (data.value i).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 89 ∧ Blank t.val 91 ∧ Blank t.val 92 ∧
      t.val.memory=s.val.memory ∧ Config layout index clock childClock t.val ∧ Frame s.val t.val := by
  have priv (j : ℕ) (h : j=88 ∨ j=90) : Private j := by
    simp only [Private,DoublingInit.Private,DoublingPass.Private]; omega
  obtain ⟨rc,r,hrc,er,r88,rr,rss,r7,rm,rcfg,rkeep,rf⟩ := read_color input tape layout data.colors
    index clock childClock i hi s cfg work.1.1 work.1.2.1 (work.1.2.2 88 (by simp [DoublingPass.Private])) rep.colors
  obtain ⟨pc,p,hpc,ep,p37,pss,p7,pm,pcfg,pf⟩ := index_executes k input tape layout index clock childClock i hw hi hlen hc
    r rcfg rss r7 (RationalAccumulator.blank_of_eq (rkeep 37 (by omega) (by omega)) work.2)
  let labels := if data.colors.get i then data.right else data.left
  have childRep : BitArray.Represents p.val.memory (childBase layout (data.colors.get i)) layout.childWidth
      (DoublingPass.words layout.childWidth labels) := by
    rw [pm,rm]
    cases hbit : data.colors.get i
    · simpa [childBase,labels,hbit] using rep.left
    · simpa [childBase,labels,hbit] using rep.right
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  have p30 : p.val.registers 30=data.colors.get i := (pf.2.2.2.2 30 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).trans rr
  have indexValue : addressValue (IncidenceEncoding.word layout.childWidth (i.val%2^k))=(childIndex k i).val := by
    apply IncidenceEncoding.word_value
    have h := (childIndex k i).isLt
    rw [hcw,pow_succ]; exact lt_of_lt_of_le h (by omega)
  obtain ⟨cc,c,hccost,ec,c90,css,c7,cm,ccfg,cf,cr⟩ := read_child k input tape layout labels (data.colors.get i)
    index clock childClock (IncidenceEncoding.word layout.childWidth (i.val%2^k)) (childIndex k i) hw indexValue hcc
    (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega) p pcfg pss p7
    (RationalAccumulator.blank_of_eq ((pf.2.2.2.1 90 (by omega) (by omega)).trans
      (rkeep 90 (by omega) (by omega))) (work.1.2.2 90 (by simp [DoublingPass.Private]))) p37 p30 childRep
  obtain ⟨lc,t,hlc,el,t90,lf⟩ := WordLift.padded_executes 90 30 (by omega) (by omega) (by omega) (by omega)
    input tape k (data.child i) (data.colors.get i) c
    (by simpa only [hcw,Data.child,labels] using c90) cr
  have keep (j : ℕ) (hj : j=4 ∨ 10≤j) (h37 : j≠37) (h88 : j≠88) (h90 : j≠90) :
      t.val.tapes j=s.val.tapes j :=
    (lf.2.2.2.2.2.1 j h90 h90).trans ((cf.2.2.2.1 j hj h90).trans
      ((pf.2.2.2.1 j hj h37).trans (rkeep j hj h88)))
  refine ⟨rc+(pc+(cc+lc)),t,?_,er.seq (ep.seq (ec.seq el)),
    BankArray.word_of_eq ((lf.2.2.2.2.2.1 88 (by omega) (by omega)).trans
      ((cf.2.2.2.1 88 (by omega) (by omega)).trans (pf.2.2.2.1 88 (by omega) (by omega)))) r88,
    BankArray.word_of_eq ((lf.2.2.2.2.2.1 37 (by omega) (by omega)).trans (cf.2.2.2.1 37 (by omega) (by omega))) p37,
    by simpa only [hw,Data.value] using t90,
    ChildPermutation.scratch_of_tapes (fun j hj => lf.2.2.2.2.2.1 j (by omega) (by omega)) css,
    RationalAccumulator.blank_of_eq (lf.2.2.2.2.2.1 7 (by omega) (by omega)) c7,
    RationalAccumulator.blank_of_eq (keep 89 (by omega) (by omega) (by omega) (by omega)) (work.1.2.2 89 (by simp [DoublingPass.Private])),
    RationalAccumulator.blank_of_eq (keep 91 (by omega) (by omega) (by omega) (by omega)) (work.1.2.2 91 (by simp [DoublingPass.Private])),
    RationalAccumulator.blank_of_eq (keep 92 (by omega) (by omega) (by omega) (by omega)) (work.1.2.2 92 (by simp [DoublingPass.Private])),
    lf.2.2.1.trans (cm.trans (pm.trans rm)),
    ccfg.of_frame (Frame.of_transfer (priv 90 (by omega)) (priv 90 (by omega)) lf),
    rf.trans ((Frame.of_except (Or.inl rfl) pf).trans ((Frame.of_except (priv 90 (by omega)) cf).trans
      (Frame.of_transfer (priv 90 (by omega)) (priv 90 (by omega)) lf)))⟩
  have hb : layout.parentWidth≤budget layout index := by dsimp [budget]; omega
  nlinarith

end Maxwell.Cost.ColorAssemble
