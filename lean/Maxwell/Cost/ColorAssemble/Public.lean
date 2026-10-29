import Maxwell.Cost.ColorAssemble.Pass

namespace Maxwell.Cost.ColorAssemble
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open ChildPermutation (Layout Config Workspace LoopFrame)

/-- Destination snapshots are proof witnesses only. The actual pass writes
every slot and requires no initial output contents. -/
theorem prepares (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : Separated layout k)
    (s : Store) (hn : Word s.val 96 (2*(2^k)).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (hcolors : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords data.colors))
    (hl : BitArray.Represents s.val.memory layout.leftForward layout.childWidth (DoublingPass.words layout.childWidth data.left))
    (hr : BitArray.Represents s.val.memory layout.rightForward layout.childWidth (DoublingPass.words layout.childWidth data.right)) :
    ∃ cost t, cost≤passCost layout k ∧ Executes input tape passCode cost s t ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory data (finalOutput layout data) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  let out : Output k := BitArray.snapshot s.val.memory layout.parentForward layout.parentWidth (2*(2^k))
  exact pass_executes k input tape layout data out clock childClock hw hc hcc hs s hn h126 cfg work
    ⟨hcolors,hl,hr,BitArray.snapshot_represents _ _ _ _⟩

/-- The one fixed compiled program reconstructs all parent labels. -/
theorem run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : Separated layout k)
    (s : Store) (hn : Word s.val 96 (2*(2^k)).bits) (h126 : Blank s.val 126)
    (cfg : Config layout [] clock childClock s.val) (work : Workspace s.val)
    (hcolors : BitArray.Represents s.val.memory layout.colors 1 (ColorPass.colorWords data.colors))
    (hl : BitArray.Represents s.val.memory layout.leftForward layout.childWidth (DoublingPass.words layout.childWidth data.left))
    (hr : BitArray.Represents s.val.memory layout.rightForward layout.childWidth (DoublingPass.words layout.childWidth data.right)) :
    ∃ t : Store,
      (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).finished=some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost layout k+1) s.val).instructions≤passCost layout k ∧
      Config layout [] clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory data (finalOutput layout data) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := prepares k input tape layout data clock childClock hw hc hcc hs s hn h126 cfg work hcolors hl hr
  have h := he.compiled_run (passCost layout k+1) (by omega)
  exact ⟨t,h.1,h.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.ColorAssemble
