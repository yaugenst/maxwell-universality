import Maxwell.Cost.SourceGraph.Retain.Core
import Maxwell.Cost.SourceGraph.Initialize
import Maxwell.Cost.SourceGraph.ExactRhs

namespace Maxwell.Cost.SourceGraph
open Structured SourceCircuit
open RationalAccumulator (Word Blank word_of_eq)

set_option maxRecDepth 16384 in
theorem Initialized.exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (Initialized.code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20=BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq first last =>
    exact (last.protectsTape 20 (by decide)).trans (Prepare.exact_rhs p S hp hm k c tape first)

theorem Initialized.Result.retain_ready {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (h : Initialized.Result S p s)
    (hrhs : s.val.tapes 20=BitTape.ofList (LogRats.records (List.ofFn S.source))) :
    Retain.Ready S p s.val := by
  obtain ⟨prepared,hprepared,pf⟩ := h.saved
  obtain ⟨square,hsquare,sf⟩ := hprepared.saved
  obtain ⟨compiled,metadata,cf⟩ := hsquare.saved
  have keep (i : ℕ) (hi : i ∈ ({19,79,80,81,82,84,86,87,95} : Finset ℕ)) :
      s.val.tapes i=compiled.val.tapes i := by
    have hlo : 19 ≤ i := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
    have hhi : i ≤ 95 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
    have h37 : i ≠ 37 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega
    exact (pf.tapes i (Or.inr (by omega)) h37 (by omega) (by omega) (by omega)).trans
      ((sf.tapes i (by simp [Prepare.work,PositiveGraph.Count.changed,PositiveGraph.Metadata.work]; omega)).trans
        (cf.tapes i (Or.inr (by omega)) (by simp [SparseEmission.work]; omega)))
  have bank : NatAssign.Bank Retain.ids (Retain.initial S p) s.val := by
    intro i hi
    by_cases big : 500 ≤ i
    · have zero : Word s.val i 0 := ⟨0,by
        simpa [BitTape.shifted,BitTape.blank] using h.fresh i (by omega) (Or.inr (by omega))⟩
      simpa [Retain.initial,show i≠19 by omega,show i≠79 by omega,show i≠84 by omega,
        show i≠82 by omega,show i≠80 by omega,show i≠81 by omega,show i≠86 by omega,show i≠87 by omega] using zero
    · simp only [Retain.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hrest
      · simpa [Retain.initial] using word_of_eq (keep 19 (by decide)) metadata.dimension
      · simpa [Retain.initial] using word_of_eq (keep 79 (by decide)) metadata.count
      · simpa [Retain.initial] using word_of_eq (keep 80 (by decide)) metadata.matrixNumerator
      · simpa [Retain.initial] using word_of_eq (keep 81 (by decide)) metadata.matrixDenominator
      · simpa [Retain.initial] using word_of_eq (keep 82 (by decide)) metadata.power
      · simpa [Retain.initial] using word_of_eq (keep 84 (by decide)) metadata.precisionWord
      · simpa [Retain.initial] using word_of_eq (keep 86 (by decide)) metadata.sourceNumerator
      · simpa [Retain.initial] using word_of_eq (keep 87 (by decide)) metadata.sourceDenominator
      · omega
  have next : BankArray.Word s.val 95
      (fixedWidth (InitializeMetadata.width S.nnz p) (Logical.sourceCircuit S p).size) :=
    BankArray.word_of_eq ((pf.tapes 95 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (sf.tapes 95 (by decide))) hsquare.next
  obtain ⟨clock,_,config⟩ := h.config
  exact ⟨bank,next,hsquare.room,hrhs,config.scratch,
    ⟨0,h.fresh 503 (by decide) (by decide)⟩,h.fresh 508 (by decide) (by decide)⟩

end Maxwell.Cost.SourceGraph
