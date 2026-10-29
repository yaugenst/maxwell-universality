import Maxwell.Cost.BinarySplit.Pipeline

namespace Maxwell.Cost.BinarySplit
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- The complete node has a literal finite instruction stream and a proved cap. -/
theorem run (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (target : Equiv.Perm (Fin (2*(2^k)))) (clock : List Bool)
    (hw : layout.route.width=k+2) (hc : clock.length=layout.route.width)
    (hs : layout.Separated (2*(2^k))) (s : Store)
    (hnword : Word s.val 96 (2*(2^k)).bits) (h94 : Blank s.val 94)
    (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout.half [] clock s.val)
    (saved : Saved layout s.val) (work : DoublingInit.Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.forward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target)))
    (hb : BitArray.Represents s.val.memory layout.backward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target.symm))) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap layout (2*(2^k)) clock+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap layout (2*(2^k)) clock+1) s.val).instructions ≤
        costCap layout (2*(2^k)) clock ∧
      DoublingPass.Config (finalLayout layout (2*(2^k))) [] clock t.val ∧
      DoublingInit.Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧
      Word t.val 96 (2*(2^k)).bits ∧ Saved layout t.val ∧
      BitArray.Represents t.val.memory (finalLayout layout (2*(2^k))).newJump 1
        (ColorPass.colorWords (colors k target)) ∧
      BitArray.Represents t.val.memory layout.forward layout.route.width
        (DoublingPass.words layout.route.width (Vector.ofFn target)) ∧
      BitArray.Represents t.val.memory layout.backward layout.route.width
        (DoublingPass.words layout.route.width (Vector.ofFn target.symm)) ∧
      CycleSplit.Frame s.val t.val ∧ MemoryFrame layout (2*(2^k)) s.val.memory t.val.memory := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes k input tape layout target clock hw hc hs s hnword h94 h95 h97 cfg saved work hf hb
  have hr := he.compiled_run (costCap layout (2*(2^k)) clock+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.BinarySplit
