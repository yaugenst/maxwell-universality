import Maxwell.Cost.SplitNode.Pipeline

namespace Maxwell.Cost.SplitNode
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

theorem run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : ChildPermutation.Data k) (clock : List Bool)
    (hcolors : data.colors=BinarySplit.colors k data.target)
    (hw : layout.split.route.width=k+2) (hc : clock.length=layout.split.route.width)
    (hs : layout.split.Separated (2*(2^k))) (hcs : (layout.child (2*(2^k))).Separated k)
    (s : Store) (hn : Word s.val 96 (2*(2^k)).bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout.split.half [] clock s.val)
    (saved : BinarySplit.Saved layout.split s.val) (work : DoublingInit.Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.split.forward layout.split.route.width
      (DoublingPass.words layout.split.route.width (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory layout.split.backward layout.split.route.width
      (DoublingPass.words layout.split.route.width (Vector.ofFn data.target.symm)))
    (bases : ∀ i : Fin 4, Word s.val (122+i.val) (layout.childBases i).bits)
    (h87 : Blank s.val 87) (h120 : Blank s.val 120) (h121 : Blank s.val 121)
    (h126 : Blank s.val 126) (h127 : Blank s.val 127) (h128 : Blank s.val 128) :
    ∃ (t : Store) (childClock : List Bool),
      (runPriced (code.compile.next input tape) (costCap layout k clock+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap layout k clock+1) s.val).instructions ≤ costCap layout k clock ∧
      ChildPermutation.Config (layout.child (2*(2^k))) [] clock childClock t.val ∧
      childClock.length=(layout.child (2*(2^k))).childWidth ∧
      ChildPermutation.Workspace t.val ∧ Blank t.val 126 ∧
      ChildPermutation.Represents (layout.child (2*(2^k))) t.val.memory data
        (ChildPermutation.finalOutputs (layout.child (2*(2^k))).childWidth data) ∧
      Word t.val 96 (2*(2^k)).bits ∧ BinarySplit.Saved layout.split t.val ∧
      Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨cost,t,childClock,hcost,he,ht⟩ := executes k input tape layout data clock hcolors hw hc hs hcs s hn h94 h95 h97
    cfg saved work hf hb bases h87 h120 h121 h126 h127 h128
  have hr := he.compiled_run (costCap layout k clock+1) (by omega)
  exact ⟨t,childClock,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.SplitNode
