import Maxwell.Cost.SourceGraph.Retain.Source

namespace Maxwell.Cost.SourceGraph.Retained
open Structured SourceCircuit
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def code (k c : ℕ) : Code := .seq (Initialized.code k c) Retain.code
noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  Initialized.totalBudget p S k c+Retain.price S (Realization.binaryCoefficientPrecision S.nnz k c)

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  data : Retain.Data S p s.val
  scratch : BankArray.Scratch s.val
  saved : ∃ previous : Store, Initialized.Result S p previous ∧ BinaryPrecision.Frame Retain.work previous.val s.val

theorem Result.fresh {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s)
    (i : ℕ) (hi : 117 ≤ i) (hout : i < 140 ∨ 163 ≤ i) (hret : i < 500 ∨ 509 < i) :
    s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes i (by simp [Retain.work]; omega)).trans (hr.fresh i hi hout)

theorem Result.io {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.inputHead=(Codec.source S).length ∧ s.val.randomCursor=0 ∧ s.val.output=[] := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hr.io.1,hf.randomCursor.trans hr.io.2.1,hf.output.trans hr.io.2.2⟩

set_option maxRecDepth 16384 in
/-- The exact RHS, source scales and dimension are retained on disjoint
banks before routing repurposes the source compiler's work tapes. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ totalBudget p S k c ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨icost,s,es,hic,hs⟩ := Initialized.executes p S hp hm hb k c tape
  have hrhs := Initialized.exact_rhs p S hp hm k c tape es
  obtain ⟨cost,t,et,hcost,ht,ts,tf⟩ := Retain.executes S _ (Codec.source S) tape s (hs.retain_ready hrhs)
  exact ⟨icost+cost,t,es.seq et,Nat.add_le_add hic hcost,ht,ts,⟨s,hs,tf⟩⟩

def program (k c : ℕ) : BitRAM := (code k c).compile

theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ t : Store, ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).finished =
        some (t.place (code k c).size) ∧
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).instructions ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  have hr := he.compiled_run (totalBudget p S k c+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.SourceGraph.Retained
