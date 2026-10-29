import Maxwell.Cost.ChildPermutation.Pass
import Maxwell.Cost.DoublingInit.Encoding

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- The four destination arrays are overwritten from arbitrary bit memory.
The snapshots are proof witnesses only; no preparatory array scan is executed. -/
theorem prepares (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : layout.Separated k)
    (s : Store) (hn : Word s.val 127 (2^k).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (hparent : BitArray.Represents s.val.memory layout.parentForward layout.parentWidth
      (DoublingPass.words layout.parentWidth (Vector.ofFn d.target)))
    (hcolors : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords d.colors)) :
    ∃ cost t, cost ≤ passCost layout k ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory d (finalOutputs layout.childWidth d) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  let out : Outputs k := fun j => BitArray.snapshot s.val.memory (layout.outputBase j) layout.childWidth (2^k)
  exact pass_executes k input tape layout d out clock childClock hw hc hcc hs s hn h126 cfg work
    ⟨hparent,hcolors,fun _ => BitArray.snapshot_represents _ _ _ _⟩

/-- Concrete compiled execution from the saved parent permutation and its
executed split colors; destination contents are unrestricted. -/
theorem run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : layout.Separated k)
    (s : Store) (hn : Word s.val 127 (2^k).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (hparent : BitArray.Represents s.val.memory layout.parentForward layout.parentWidth
      (DoublingPass.words layout.parentWidth (Vector.ofFn d.target)))
    (hcolors : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords d.colors)) :
    ∃ t : Store,
      (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).finished =
        some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).instructions ≤ passCost layout k ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory d (finalOutputs layout.childWidth d) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := prepares k input tape layout d clock childClock hw hc hcc hs
    s hn h126 cfg work hparent hcolors
  have hr := he.compiled_run (passCost layout k+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.ChildPermutation
