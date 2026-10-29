import Maxwell.Cost.SourceCircuit.CompileSource.Bounds

namespace Maxwell.Cost.SourceCircuit.CompileSource
open Structured

def program (k c : ℕ) : BitRAM := (code k c).compile

set_option maxRecDepth 16384 in
theorem bounded_executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost pre allocated start t roots,
      Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ totalBudget p S k c ∧
      Preparation.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val ∧
      AllocateSource.Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory allocated ∧
      AllocationPass.Persistent pre allocated ∧ BinaryPrecision.Frame ArithmeticPrelude.work allocated.val start.val ∧
      ArithmeticPass.Persistent start t ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots pre.val.memory t := by
  obtain ⟨cost,pre,allocated,start,t,roots,he,hcost,hpre,ha,fpa,fas,fst,ht⟩ :=
    executes p S hp hm hb k c tape
  have hpass := passPrice_bound S (Realization.binaryCoefficientPrecision S.nnz k c)
    (Source.dimension_le_nnz S hp.1) (by omega) (Realization.binaryCoefficientPrecision_pos _ _ _)
    roots pre.val.memory allocated ha
  have htotal := hcost.trans ((Nat.add_le_add_left hpass _).trans (total_bound p S hp k c))
  exact ⟨cost,pre,allocated,start,t,roots,he,htotal,hpre,ha,fpa,fas,fst,ht⟩

set_option maxRecDepth 16384 in
/-- The entire source circuit compiler halts within a source-only
near-linear bit cap for every random tape. It consumes no random input. -/
theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ t : Store, ∃ roots : RootInitData S.n, ∃ memory : ℕ → Bool,
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).finished =
        some (t.place (code k c).size) ∧
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).instructions ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) roots memory t ∧
      t.val.inputHead = (Codec.source S).length ∧ t.val.randomCursor = 0 ∧ t.val.output = [] := by
  obtain ⟨cost,pre,allocated,start,t,roots,he,hcost,hpre,_,fpa,fas,fst,ht⟩ :=
    bounded_executes p S hp hm hb k c tape
  have hr := he.compiled_run (totalBudget p S k c+1) (by omega)
  refine ⟨t,roots,pre.val.memory,hr.1,?_,ht,
    fst.inputHead.trans (fas.inputHead.trans (fpa.inputHead.trans hpre.inputHead)),
    fst.randomCursor.trans (fas.randomCursor.trans (fpa.randomCursor.trans hpre.randomCursor)),
    fst.output.trans (fas.output.trans (fpa.output.trans hpre.output))⟩
  have charged : ((program k c).run (Codec.source S) tape
      (totalBudget p S k c+1)).instructions = cost := hr.2
  rw [charged]
  exact hcost

end Maxwell.Cost.SourceCircuit.CompileSource
