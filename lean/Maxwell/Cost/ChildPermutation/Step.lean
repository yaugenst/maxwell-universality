import Maxwell.Cost.ChildPermutation.Read
import Maxwell.Cost.ChildPermutation.SelectBinding
import Maxwell.Cost.ChildPermutation.Write
import Maxwell.Cost.ChildPermutation.Cleanup

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open Maxwell.Logical.Routing.Coloring.NumericSplit

def stepCode : Code := .seq readCode (.seq selectPairCode
  (.seq (BankArray.packCanonicalCode 81 121) (.seq writeCode cleanupCode)))

/-- One fixed source-pair iteration emits both child labels and their
inverse entries, then erases every transient word. -/
theorem step_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (out : Outputs k) (index clock childClock : List Bool)
    (i : Fin (2^k)) (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.childWidth) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : layout.Separated k)
    (s : Store) (cfg : Config layout index clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory data out) :
    ∃ cost t, cost≤500000*(budget layout index+1)^2 ∧ Executes input tape stepCode cost s t ∧
      Config layout index clock childClock t.val ∧ Workspace t.val ∧
      t.val.memory=stepMemory layout data i s.val.memory ∧
      Represents layout t.val.memory data (stepOutputs layout.childWidth data i out) ∧
      Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  obtain ⟨rc,r,hrc,er,r88,r89,r91,rss,r7,r37,r90,r92,rm,rcfg,rf⟩ :=
    read_executes k input tape layout data out index clock childClock i hw hi (by omega) hc s cfg work rep
  obtain ⟨ac,a,hac,ea,a89,a91,a92,ass,a7,am,acfg,akeep,af⟩ :=
    select_pair k input tape layout data index clock childClock i hw r rcfg r88 r89 r91 r92 rss r7
  obtain ⟨pc,p,hpc,ep,p37,pss,p7,pm,pf⟩ := BankArray.pack_canonical 81 121 (by omega) (by omega)
    input tape index childClock (by omega) (by omega) a ass a7
      (RationalAccumulator.blank_of_eq (akeep 37 (by omega) (by omega) (by omega)) r37) acfg.index acfg.childClock
  have wordI : FixedWidth.bits childClock.length index=IncidenceEncoding.word layout.childWidth i.val := by
    apply SourceCircuit.fixedWidth_eq
    · simp [hcc]
    · rw [FixedWidth.bits_value _ _ (by omega),hi]
  have pcfg := acfg.of_frame (Frame.of_except (Or.inl rfl) pf)
  have prep : Represents layout p.val.memory data out := by simpa only [pm.2.2.2.1,am,rm] using rep
  obtain ⟨wc,w,hwc,ew,wm,wr,wcfg,wss,w7,w89,w91,w37,wf,wmem,wbank⟩ := write_executes input tape layout data out i
    index clock childClock hw hi hs p pcfg pss p7
    (BankArray.word_of_eq (pf.2.2.2.1 89 (by omega) (by omega)) a89)
    (BankArray.word_of_eq (pf.2.2.2.1 91 (by omega) (by omega)) a91)
    (by simpa only [wordI] using p37) prep
  have w88 := BankArray.word_of_eq ((wbank.2.2.2.1 88 (by omega)).trans
    ((pf.2.2.2.1 88 (by omega) (by omega)).trans (akeep 88 (by omega) (by omega) (by omega)))) r88
  have w90 := RationalAccumulator.blank_of_eq ((wbank.2.2.2.1 90 (by omega)).trans
    ((pf.2.2.2.1 90 (by omega) (by omega)).trans (akeep 90 (by omega) (by omega) (by omega)))) r90
  obtain ⟨t,et,tw,tm,tf⟩ := cleanup_executes input tape [data.colors.get (lower i)]
    (IncidenceEncoding.word layout.childWidth (data.left i).val)
    (IncidenceEncoding.word layout.childWidth (data.right i).val)
    (IncidenceEncoding.word layout.childWidth i.val) w w88 w89 w91 w37 w90
    (RationalAccumulator.blank_of_eq ((wbank.2.2.2.1 92 (by omega)).trans
      (pf.2.2.2.1 92 (by omega) (by omega))) a92) wss w7
  refine ⟨rc+(ac+(pc+(wc+(6*([data.colors.get (lower i)].length+
    (IncidenceEncoding.word layout.childWidth (data.left i).val).length+
    (IncidenceEncoding.word layout.childWidth (data.right i).val).length+
    (IncidenceEncoding.word layout.childWidth i.val).length)+24)))),t,?_,
    er.seq (ea.seq (ep.seq (ew.seq et))),wcfg.of_frame tf,tw,?_,?_,
    rf.trans (af.trans ((Frame.of_except (Or.inl rfl) pf).trans (wf.trans tf))),?_⟩
  · have hp : layout.parentWidth≤budget layout index := by dsimp [budget]; omega
    have hchild : layout.childWidth≤budget layout index := by dsimp [budget]; omega
    simp only [List.length_cons,List.length_nil,IncidenceEncoding.word_length]
    nlinarith
  · rw [tm,wm,pm.2.2.2.1,am,rm]
  · simpa only [tm] using wr
  · simpa only [tm,pm.2.2.2.1,am,rm] using wmem

end Maxwell.Cost.ChildPermutation
