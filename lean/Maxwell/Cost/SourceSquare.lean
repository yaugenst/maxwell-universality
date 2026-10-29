import Maxwell.Cost.SourceSquare.Asymptotics
import Maxwell.Cost.SourceCircuit.CompileSourceTrace
import Maxwell.Cost.SourceCircuit.FinalMetadata
import Maxwell.Cost.SparseEmission

namespace Maxwell.Cost.SourceSquare
open Structured SourceCircuit
open RationalAccumulator (Blank Word word_of_eq)

def code (k c : ℕ) : Code := .seq (CompileSource.code k c) SparseEmission.code
def program (k c : ℕ) : BitRAM := (code k c).compile

/-- The concrete sparse square system and retained source quantities after
the compiler and sparse emission have both executed. -/
structure Result (S : Source.SparseSystem) (precision : ℕ) (s : Store) : Prop where
  archive : s.val.tapes 110 = BitTape.shifted
    (SparseEmission.entriesWire (InitializeMetadata.width S.nnz precision)
      (Logical.sourceSquareEntries S precision))
    (-(SparseEmission.entriesWire (InitializeMetadata.width S.nnz precision)
      (Logical.sourceSquareEntries S precision)).length)
  next : BankArray.Word s.val 95 (fixedWidth (InitializeMetadata.width S.nnz precision)
    (Logical.sourceCircuit S precision).size)
  room : (Logical.sourceCircuit S precision).size < 2^InitializeMetadata.width S.nnz precision
  scratch : BankArray.Scratch s.val
  blank7 : Blank s.val 7
  blank37 : Blank s.val 37
  clean : s.val.tapes 105 = BitTape.blank ∧ s.val.tapes 111 = BitTape.blank ∧
    s.val.tapes 112 = BitTape.blank ∧ s.val.tapes 114 = BitTape.blank
  saved : ∃ previous : Store, FinalMetadata.Metadata S precision previous ∧
    SparseEmission.OutputFrame previous.val s.val

theorem Result.dimension {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result S precision s) : Word s.val 19 S.n := by
  obtain ⟨previous,hm,hf⟩ := h.saved
  exact word_of_eq (hf.tapes 19 (by decide) (by decide)) hm.dimension

theorem Result.count {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result S precision s) : Word s.val 79 S.nnz := by
  obtain ⟨previous,hm,hf⟩ := h.saved
  exact word_of_eq (hf.tapes 79 (by decide) (by decide)) hm.count

theorem Result.widthWord {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result S precision s) : Word s.val 90 (InitializeMetadata.width S.nnz precision) := by
  obtain ⟨previous,hm,hf⟩ := h.saved
  exact word_of_eq (hf.tapes 90 (by decide) (by decide)) hm.widthWord

theorem Result.io {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result S precision s) : s.val.inputHead = (Codec.source S).length ∧
      s.val.randomCursor = 0 ∧ s.val.output = [] := by
  obtain ⟨previous,hm,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hm.inputHead,hf.randomCursor.trans hm.randomCursor,
    hf.output.trans hm.output⟩

theorem Result.fresh {S : Source.SparseSystem} {precision : ℕ} {s : Store}
    (h : Result S precision s) (i : ℕ) (hi : 116 ≤ i) : s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hm,hf⟩ := h.saved
  exact (hf.tapes i (Or.inr (by omega)) (by simp [SparseEmission.work]; omega)).trans
    (hm.fresh i (by omega))

/-- The archive emitted by the arithmetic compiler is consumed directly;
neither an entry list nor a matrix is supplied as an extra machine input. -/
theorem emit (S : Source.SparseSystem) (precision : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hm : FinalMetadata.Metadata S precision s)
    (ha : CompileSourceTrace.Archives S precision s) :
    ∃ cost t, Executes input tape SparseEmission.code cost s t ∧
      cost ≤ emissionBudget S precision ∧ Result S precision t := by
  obtain ⟨bytes,hbytes,h97⟩ := ha.gates
  obtain ⟨clockOrigin,hclock⟩ := hm.clock
  have h105 : s.val.tapes 105 = BitTape.atEnd
      ((List.ofFn (fun i : Fin S.n => (Logical.sourceOutput S precision i).val)).flatMap
        (fixedWidth (InitializeMetadata.width S.nnz precision))) := by
    rw [CompileSourceInitial.sourceOutput_list]
    exact ha.outputs
  obtain ⟨cost,t,hcost,he,archive,h105,h111,h112,h114,hs,h7,h37,hf⟩ :=
    SparseEmission.executes (Logical.sourceCircuit_rational S precision).code
      (Logical.sourceOutput S precision) input tape (InitializeMetadata.width S.nnz precision)
      bytes (AllocateSource.clock S precision) clockOrigin s
      (InitializeMetadata.width_pos _ _) ha.room (AllocateSource.clock_length S precision)
      hbytes hm.scratch hm.blank7 hm.blank37 hm.dimension hclock h97 h105
      (hm.fresh 110 (by decide)) (hm.fresh 111 (by decide)) (hm.fresh 112 (by decide))
      (hm.fresh 113 (by decide)) (hm.fresh 114 (by decide)) (hm.fresh 115 (by decide))
  refine ⟨cost,t,he,hcost,archive,?_,ha.room,hs,h7,h37,⟨h105,h111,h112,h114⟩,⟨s,hm,hf⟩⟩
  obtain ⟨origin,hn⟩ := ha.next
  exact ⟨origin,(hf.tapes 95 (by decide) (by decide)).trans hn⟩

set_option maxRecDepth 16384 in
/-- One fixed program reads only the canonical sparse source and computes
the complete sparse square system, with a uniform source-only bit bound. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t ∧ cost ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨cost,pre,allocated,start,compiled,roots,he,hcost,hpre,ha,fpa,fas,fst,ht⟩ :=
    CompileSource.bounded_executes p S hp hm hb k c tape
  have metadata := FinalMetadata.preserved S _ roots pre allocated start compiled
    hpre ha fpa fas fst ht
  have archives := CompileSourceTrace.archives S _ hp.1 (by omega)
    (Realization.binaryCoefficientPrecision_pos _ _ _) roots pre.val.memory allocated compiled ha ht
  obtain ⟨extra,t,ee,hextra,hresult⟩ := emit S _ (Codec.source S) tape compiled metadata archives
  exact ⟨cost+extra,t,he.seq ee,
    (Nat.add_le_add hcost hextra).trans (total_bound p S hp k c),hresult⟩

set_option maxRecDepth 16384 in
theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ t : Store,
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).finished =
        some (t.place (code k c).size) ∧
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).instructions ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t ∧
      t.val.inputHead = (Codec.source S).length ∧ t.val.randomCursor = 0 ∧ t.val.output = [] := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  have hr := he.compiled_run (totalBudget p S k c+1) (by omega)
  refine ⟨t,hr.1,?_,ht,ht.io⟩
  have charged : ((program k c).run (Codec.source S) tape
      (totalBudget p S k c+1)).instructions = cost := hr.2
  rw [charged]
  exact hcost

end Maxwell.Cost.SourceSquare
