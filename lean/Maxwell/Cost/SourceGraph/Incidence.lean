import Maxwell.Cost.SourceGraph.Incidence.Encoding
import Maxwell.Cost.GraphIncidence.Complexity

namespace Maxwell.Cost.SourceGraph.Incidence
open Structured PositiveGraph Maxwell.Cost.SourceGraph.Positive
open Maxwell.Logical.Routing
open RationalAccumulator (Word Blank word_of_eq)

def phaseBudget (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  400000*(4*count S p+1)*
    (IncidencePass.budget (GraphIncidence.layout (width S p) (dimension S p) (count S p))
      (4*count S p).bits+(width S p+3)+5+1)^2

def code (k c : ℕ) : Code := .seq (Positive.code k c) GraphIncidence.passCode
noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  Positive.totalBudget p S k c+phaseBudget S (Realization.binaryCoefficientPrecision S.nnz k c)

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  room : dimension S p < 2^width S p
  data : Retain.Data S p s.val
  numeric : Metadata.Numeric (width S p) (dimension S p) (count S p) s.val
  incidence : IncidenceEncoding.Represents (GraphIncidence.layout (width S p) (dimension S p) (count S p))
    s.val.memory (endpoint S p) (IncidenceRanks.run (endpoint S p) (4*count S p) le_rfl)
  diagonal : BitArray.Represents s.val.memory (base S p) 4 (Invariant.sourceDiagonalWords S p)
  configuration : ∃ clock index, clock.length=width S p+3 ∧ addressValue index=4*count S p ∧
    index.length≤(4*count S p).bits.length ∧
    IncidencePass.Config (GraphIncidence.layout (width S p) (dimension S p) (count S p)) index clock
      (s.renameTapes GraphIncidence.relocation.symm).val ∧
    IncidencePass.Workspace (s.renameTapes GraphIncidence.relocation.symm).val
  saved : ∃ previous : Store, Positive.Result S p previous ∧
    SourceCircuit.Frame (Finset.Icc 600 612) previous.val s.val

theorem Result.fresh {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s)
    (i : ℕ) (hi : 163 ≤ i) (hret : i < 500 ∨ 509 < i) (hout : i < 600 ∨ 612 < i) :
    s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes i (Or.inr (by omega)) (by simp; omega)).trans (hr.fresh i hi hret)

theorem Result.io {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.inputHead=(Codec.source S).length ∧ s.val.randomCursor=0 ∧ s.val.output=[] := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hr.io.1,hf.randomCursor.trans hr.io.2.1,hf.output.trans hr.io.2.2⟩

/-- The canonical source's endpoint array is consumed directly by the
executed incidence counter pass. Fresh banks avoid modifying source archives. -/
theorem emit (S : Source.SparseSystem) (p : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hs : Positive.Result S p s) :
    ∃ cost t, Executes input tape GraphIncidence.passCode cost s t ∧
      cost≤phaseBudget S p ∧ Result S p t := by
  obtain ⟨clock,hclockLength,hclock⟩ := hs.clock
  obtain ⟨cost,t,index,hcost,et,hi,hilen,config,workspace,_blank,represented,frame,memoryFrame⟩ :=
    GraphIncidence.pass_executes (width S p) (dimension S p) (count S p) clock (endpoint S p)
      input tape s hs.numeric hclock hclockLength
      (fun i hi _ => ⟨0,hs.fresh i (by omega) (Or.inr (by omega))⟩)
      hs.workspace.scratch hs.workspace.sample (vertex_fit hs) (endpoint_degree S p) (initial_representation hs)
  have budget : cost≤phaseBudget S p := by
    have h := hcost.trans (GraphIncidence.passCost_bound (width S p) (dimension S p) (count S p) clock)
    simpa only [phaseBudget,GraphIncidence.budget,hclockLength] using h
  have numeric := hs.numeric.transport (fun i hlo hhi _ => frame.tapes i (Or.inr (by omega))
    (by simp; omega))
  have data : Retain.Data S p t.val :=
    ⟨hs.data.numeric.transport (fun i hlo hhi _ _ => frame.tapes i (Or.inr (by omega)) (by simp; omega)),
      word_of_eq (frame.tapes 503 (by decide) (by decide)) hs.data.circuitSize,
      (frame.tapes 508 (by decide) (by decide)).trans hs.data.rhs⟩
  have diagonal := memoryFrame.represents_after
    (show (GraphIncidence.layout (width S p) (dimension S p) (count S p)).baseCounter+
      (2*dimension S p+count S p)*2 ≤ base S p by dsimp [GraphIncidence.layout,base]; omega)
    (show (GraphIncidence.layout (width S p) (dimension S p) (count S p)).baseRank+
      4*count S p*2 ≤ base S p by dsimp [GraphIncidence.layout,base]; omega) hs.diagonal
  exact ⟨cost,t,et,budget,hs.room,data,numeric,represented,diagonal,
    ⟨clock,index,hclockLength,hi,hilen,config,workspace⟩,⟨s,hs,frame⟩⟩

set_option maxRecDepth 16384 in
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost≤totalBudget p S k c ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨pcost,s,es,hpc,hs⟩ := Positive.executes p S hp hm hb k c tape
  obtain ⟨cost,t,et,hcost,ht⟩ := emit S _ (Codec.source S) tape s hs
  exact ⟨pcost+cost,t,es.seq et,Nat.add_le_add hpc hcost,ht⟩

def program (k c : ℕ) : BitRAM := (code k c).compile

theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ t : Store, ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).finished =
        some (t.place (code k c).size) ∧
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).instructions≤totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  have hr := he.compiled_run (totalBudget p S k c+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.SourceGraph.Incidence
