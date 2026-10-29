import Maxwell.Cost.ColorAssemble.Loop

namespace Maxwell.Cost.ColorAssemble
open Structured
open ChildPermutation (Layout Config Workspace LoopFrame budget config_update workspace_update)
open BankArray (Word)
open RationalAccumulator (Blank)

/-- The saved parent length supplies the actual countdown. The completed
index is erased so the same static program can process the next routing node. -/
def passCode : Code := .seq (.call (WordTransfer.clone 96 126))
  (.seq loopCode (.call (TapeOps.clear 81)))

def passCost (layout : Layout) (k : ℕ) : ℕ := loopCost layout k+21*(2*((2:ℕ)^k)).bits.length+21

theorem pass_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (out : Output k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : Separated layout k)
    (s : Store) (hn : Word s.val 96 (2*((2:ℕ)^k)).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory d out) :
    ∃ cost t, cost ≤ passCost layout k ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory d (finalOutput layout d) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨no,hnw⟩ := hn
  obtain ⟨co,hcount⟩ := h126
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 96 126 (by omega) input tape (2*((2:ℕ)^k)).bits no co s hnw hcount
  have keep (i : ℕ) (hi : i ≠ 126) : a.val.tapes i=s.val.tapes i := by simp [atapes,hi]
  have acfg := config_update (fun i _ hi => keep i hi) cfg
    (BankArray.word_of_eq (keep 81 (by omega)) cfg.index)
  have awork := workspace_update (fun i _ hi => keep i hi) work
  have arep : Represents layout a.val.memory d out := by simpa only [af.2.2.1] using rep
  obtain ⟨pcost,p,index,hpcost,ep,_,hlen,pcfg,pwork,p126,prep,pframe,pmemory⟩ :=
    loop_executes k input tape layout d out [] clock childClock hw hc hcc hs rfl (by simp)
      co a (by simp [atapes]) acfg awork arep
  obtain ⟨io,hiword⟩ := pcfg.index
  obtain ⟨t,et,ttapes,tf⟩ := WordCall.clear 81 input tape index io p hiword
  have tkeep (i : ℕ) (hi : i ≠ 81) : t.val.tapes i=p.val.tapes i := by simp [ttapes,hi]
  have tc : Config layout [] clock childClock t.val :=
    config_update (fun i hi _ => tkeep i hi) pcfg
      ⟨io+index.length,by simp [ttapes,BitTape.shifted,BitTape.blank]⟩
  have tw := workspace_update (fun i hi _ => tkeep i hi) pwork
  have frameA : LoopFrame s.val a.val :=
    ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,fun i _ _ hi _ => keep i hi,
      fun i _ hr => af.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩
  have frameT : LoopFrame p.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ hi _ _ => tkeep i hi,
      fun i _ hr => tf.2.2.2.2.2.2 i (by omega) (by omega)⟩
  refine ⟨15*(2*((2:ℕ)^k)).bits.length+17+(pcost+(6*index.length+4)),t,?_,ea.seq (ep.seq et),tc,tw,
    RationalAccumulator.blank_of_eq (tkeep 126 (by omega)) p126,?_,frameA.trans (pframe.trans frameT),?_⟩
  · dsimp [passCost]; omega
  · simpa only [tf.2.2.1] using prep
  · simpa only [tf.2.2.1,af.2.2.1] using pmemory

/-- Full finite-program termination and charged execution, with exact assembled parent
routing labels in bit memory. -/
theorem pass_run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (out : Output k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : Separated layout k)
    (s : Store) (hn : Word s.val 96 (2*((2:ℕ)^k)).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory d out) :
    ∃ t : Store, (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).finished =
        some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).instructions ≤ passCost layout k ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory d (finalOutput layout d) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := pass_executes k input tape layout d out clock childClock
    hw hc hcc hs s hn h126 cfg work rep
  have hr := he.compiled_run (passCost layout k+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.ColorAssemble
