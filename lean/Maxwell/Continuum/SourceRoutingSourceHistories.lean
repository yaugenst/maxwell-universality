import Maxwell.Continuum.SourceRoutingSourcePhasePrepare

/-! A single source-driven program builds the permutation, its recursive
colors, and all three sorting histories used to emit the geometry. -/
namespace Maxwell.Cost.RoutingPorts.Complete.SourceHistories
open Structured Maxwell.Logical.Routing SourcePhase
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq SourcePhase.prepareCode GeometryHistories.fromArraysCode
def work : Finset ℕ := SourcePhase.prepareWork∪GeometryHistories.fromArraysWork
def cost (S : Source.SparseSystem) (p : ℕ)
    (room : SourceGraph.Positive.dimension S p<2^SourceGraph.Positive.width S p) : ℕ :=
  SourcePhase.prepareCost S p room+GeometryHistories.fromArraysCost (SourcePhase.plan S p)

theorem executes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost S p hs.room ∧
      GeometryHistory.Runtime (GeometryHistories.historyPlan (plan S p) 2)
        (GeometryHistories.keys (Composition.SourceRouting.indexedData S p).colors 2) (2*side S p) t ∧
      Blank t.val 1241 ∧ GeometryHistories.Stored (plan S p)
        (Composition.SourceRouting.indexedData S p).colors t.val.memory ∧
      BitArray.Represents t.val.memory (layout S p).backward (plan S p).width
        (IncidenceEncoding.words (plan S p).width
          (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target.symm)) ∧
      Word t.val 717 (layout S p).backward ∧
      ArchiveFrame work s.val t.val ∧
      (∀address,address<(SourcePlan.treeLayout S p).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c0,a,e0,h0,ra,f0,m0⟩:=prepare_executes S p hm input tape s hs
  obtain ⟨c1,t,e1,h1,rt,t1241,histories,f1,m1⟩:=GeometryHistories.from_arrays_executes (plan S p)
    (sequential S p) (base_order S p) (Composition.SourceRouting.indexedData S p).colors input tape a
    ra.bank ra.ready ra.privateBlank ra.metadata ra.count ra.innerBlank ra.outerBlank ra.targets ra.labels
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,rt,t1241,histories,
    ra.inverse.prefix m1 (backward_before S p),
    RationalAccumulator.word_of_eq (f1.tapes 717 (by decide) (by decide +kernel)) ra.backwardWord,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right),?_⟩
  intro address ha
  exact (m1 address (ha.trans_le (forward_before S p))).trans (m0 address ha)

#print axioms executes

theorem numeric {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : PositiveGraph.Metadata.Numeric (SourceGraph.Positive.width S p)
      (SourceGraph.Positive.dimension S p) (SourceGraph.Positive.count S p) s.val)
    (hf : ArchiveFrame work s.val t.val) :
    PositiveGraph.Metadata.Numeric (SourceGraph.Positive.width S p)
      (SourceGraph.Positive.dimension S p) (SourceGraph.Positive.count S p) t.val := by
  apply hs.transport
  intro i hlo hhi _
  apply hf.tapes i (Or.inr (by omega))
  have disjoint : Disjoint (Finset.Icc 140 159) work := by decide +kernel
  exact Finset.disjoint_left.mp disjoint (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)

theorem retained {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Retain.Data S p s.val) (hf : ArchiveFrame work s.val t.val) :
    SourceGraph.Retain.Data S p t.val := by
  have keep (i : ℕ) (hlo : 500≤ i) (hhi : i≤509) : t.val.tapes i=s.val.tapes i := by
    apply hf.tapes i (Or.inr (by omega))
    have disjoint : Disjoint (Finset.Icc 500 509) work := by decide +kernel
    exact Finset.disjoint_left.mp disjoint (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)
  exact ⟨hs.numeric.transport (fun i hlo hhi _ _=>keep i hlo hhi),
    RationalAccumulator.word_of_eq (keep 503 (by decide) (by decide)) hs.circuitSize,
    (keep 508 (by decide) (by decide)).trans hs.rhs⟩

#print axioms numeric
#print axioms retained
end Maxwell.Cost.RoutingPorts.Complete.SourceHistories
