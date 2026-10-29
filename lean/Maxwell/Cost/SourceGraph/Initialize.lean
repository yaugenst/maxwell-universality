import Maxwell.Cost.SourceGraph.Prepare
import Maxwell.Cost.PositiveGraph.Metadata.ArrayBounds

namespace Maxwell.Cost.SourceGraph.Initialized
open Structured SourceCircuit
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

private abbrev W (S : Source.SparseSystem) (p : ℕ) := InitializeMetadata.width S.nnz p
private abbrev d (S : Source.SparseSystem) (p : ℕ) := (Logical.sourceCircuit S p).size
private abbrev K (S : Source.SparseSystem) (p : ℕ) := (Logical.sourceSquareEntries S p).length

def initializationPrice (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  PositiveGraph.Initialize.costCap (d S p) (K S p) (PositiveGraph.Metadata.arrayBudget (W S p))
def code (k c : ℕ) : Code := .seq (Prepare.code k c) PositiveGraph.Initialize.code
noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  Prepare.totalBudget p S k c+initializationPrice S (Realization.binaryCoefficientPrecision S.nnz k c)

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  config : ∃ clock, clock.length=W S p+3 ∧ PositiveGraph.Initialize.Config (W S p) (d S p) (K S p) 0 clock s.val
  arrays : PositiveGraph.Initialize.Arrays (W S p) (d S p) (K S p) s.val.memory
  saved : ∃ previous : Store, Prepare.Result S p previous ∧ PositiveGraph.Initialize.Frame previous.val s.val

theorem Result.fresh {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s)
    (i : ℕ) (hi : 117 ≤ i) (hout : i < 140 ∨ 163 ≤ i) : s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes i (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega)).trans
    (hr.fresh i hi (by omega))

theorem Result.archive {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.tapes 110 = BitTape.shifted
      (SparseEmission.entriesWire (W S p) (Logical.sourceSquareEntries S p))
      (-(SparseEmission.entriesWire (W S p) (Logical.sourceSquareEntries S p)).length) := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes 110 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr.archive

theorem Result.io {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.inputHead=(Codec.source S).length ∧ s.val.randomCursor=0 ∧ s.val.output=[] := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hr.io.1,hf.randomCursor.trans hr.io.2.1,hf.output.trans hr.io.2.2⟩

/-- All four graph arrays are initialized by actual writes, even when the
compiler's earlier arrays occupy the same memory addresses. -/
theorem from_prepare (S : Source.SparseSystem) (p : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Prepare.Result S p s) :
    ∃ cost t, Executes input tape PositiveGraph.Initialize.code cost s t ∧
      cost ≤ initializationPrice S p ∧ Result S p t := by
  obtain ⟨clock,hclock,hword⟩ := hs.clock
  obtain ⟨previous,hprevious,_⟩ := hs.saved
  have hb := PositiveGraph.Metadata.array_bounds (W S p) (d S p) (K S p)
    hprevious.room (Prepare.count_bound S p hprevious.room)
  have hc : PositiveGraph.Initialize.Config (W S p) (d S p) (K S p) 0 clock s.val :=
    ⟨hs.numeric,hword,hs.scratch,hs.blank7,hs.blank37,
      ⟨0,hs.fresh 160 (by decide) (by decide)⟩,
      ⟨0,hs.fresh 161 (by decide) (by decide)⟩,
      ⟨0,by simpa [BitTape.shifted,BitTape.blank] using hs.fresh 162 (by decide) (by decide)⟩⟩
  obtain ⟨cost,t,hcost,et,ht,arrays,_outside,hframe⟩ := PositiveGraph.Initialize.executes
    (W S p) (d S p) (K S p) (PositiveGraph.Metadata.arrayBudget (W S p))
    clock hclock hb input tape s hc
  exact ⟨cost,t,et,hcost,⟨clock,hclock,ht⟩,arrays,⟨s,hs,hframe⟩⟩

set_option maxRecDepth 16384 in
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ totalBudget p S k c ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨pcost,s,es,hpc,hs⟩ := Prepare.executes p S hp hm hb k c tape
  obtain ⟨cost,t,et,hcost,ht⟩ := from_prepare S _ (Codec.source S) tape s hs
  exact ⟨pcost+cost,t,es.seq et,Nat.add_le_add hpc hcost,ht⟩

def program (k c : ℕ) : BitRAM := (code k c).compile

end Maxwell.Cost.SourceGraph.Initialized
