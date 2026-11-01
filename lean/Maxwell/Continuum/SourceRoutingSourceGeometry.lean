import Maxwell.Continuum.SourceRoutingSourceHistories
import Maxwell.Continuum.SourceRoutingGeometryProducer
import Maxwell.Cost.SourceGraph.Retain.Transport

/-! Complete source-driven geometry compilation: permutation, recursive
colors, three sorting histories, and every packed vertex/path record. -/
namespace Maxwell.Cost.RoutingPorts.Complete.SourceGeometry
open Structured Maxwell.Logical Maxwell.Logical.Routing Maxwell.Composition
open SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def history (S : Source.SparseSystem) (p : ℕ) : GeometryHistory.Plan (SourcePhase.side S p) :=
  GeometryHistories.historyPlan (SourcePhase.plan S p) 0
def backward (S : Source.SparseSystem) (p : ℕ) : ℕ := (SourcePhase.layout S p).backward

theorem history_start (S : Source.SparseSystem) (p : ℕ) :
    (history S p).base=backward S p+12*(history S p).stride := by
  change backward S p+11*(SourcePhase.side S p*SourcePhase.side S p*
    (SourcePhase.side S p*SourcePhase.side S p).bits.length)+
      SourcePhase.side S p*SourcePhase.side S p*(SourcePhase.side S p*SourcePhase.side S p).bits.length=_
  unfold GeometryHistory.Plan.stride GeometryHistory.Plan.width
  ring

def plan (S : Source.SparseSystem) (p : ℕ) : GeometryEmission.Plan (SourcePhase.side S p) :=
  GeometryStartup.plan (history S p) (backward S p) (history_start S p)
def code : Code := .seq SourceHistories.code GeometryProducer.code
def work : Finset ℕ := SourceHistories.work∪GeometryProducer.work
def cost (S : Source.SparseSystem) (p : ℕ)
    (room : SourceGraph.Positive.dimension S p<2^SourceGraph.Positive.width S p) : ℕ :=
  SourceHistories.cost S p room+GeometryProducer.price S p (history S p) (backward S p) (history_start S p)

theorem executes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost S p hs.room ∧
      GeometryEmission.State (SourceRouting.indexedData S p) (plan S p)
        (packedLength (SourceEmission.geometry S p)) (GeometryProducer.edges S p) t ∧
      Blank t.val 1258 ∧
      StoredGeometry (SourceEmission.geometry S p) (GeometryStartup.outputBase (history S p))
        (GeometryStartup.outputWidth (history S p)) t.val.memory ∧
      Represents S p (SourceEmission.geometry S p) ∧ ArchiveFrame work s.val t.val ∧
      (∀address,address<(SourcePlan.treeLayout S p).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c₀,a,e₀,h₀,runtime,_,histories,inverse,backwardWord,f₀,m₀⟩:=
    SourceHistories.executes S p hm input tape s hs
  have seq:=SourcePhase.sequential S p
  have hr : (history S p).following.following=GeometryHistories.historyPlan (SourcePhase.plan S p) 2 := by
    rw [history,seq.1,seq.2]
  have last : GeometryHistory.Runtime (history S p).following.following
      (PhaseKeys.last (SourceRouting.indexedData S p).colors) (2*SourcePhase.side S p) a := by
    rw [hr]
    exact runtime
  have second : GeometryHistory.Stored (history S p).following
      (PhaseKeys.middle (SourceRouting.indexedData S p).colors) (2*SourcePhase.side S p) a.val.memory := by
    rw [history,seq.1]
    exact histories 1
  have fresh : ∀i∈GeometryStartup.freshPorts,Blank a.val i := by
    intro i hi
    have low : 1242 ≤ i := by
      simp only [GeometryStartup.freshPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    have disjoint : Disjoint GeometryStartup.freshPorts SourceHistories.work := by decide +kernel
    exact RationalAccumulator.blank_of_eq
      (f₀.tapes i (Or.inr (by omega)) (Finset.disjoint_left.mp disjoint hi))
      ⟨0,hs.fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega))⟩
  have numeric:=SourceHistories.numeric hs.numeric f₀
  obtain ⟨c₁,t,e₁,h₁,state,blank,stored,represented,f₁,m₁⟩:=GeometryProducer.executes S p
    (history S p) (backward S p) (history_start S p) input tape a last backwardWord (histories 0)
    second inverse fresh
    (by simpa only [SourceGraph.Positive.dimension,SourceGraph.Positive.count,GeometryProducer.vertices,
      Nat.two_mul] using numeric.vertices)
    (by simpa only [SourceGraph.Positive.dimension,Nat.two_mul] using numeric.doubledDimension)
    (by simpa only [SourceGraph.Positive.count,GeometryProducer.edges,Nat.two_mul] using numeric.edges)
  refine ⟨c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,state,blank,stored,represented,
    (f₀.mono Finset.subset_union_left).trans (f₁.mono Finset.subset_union_right),?_⟩
  intro address ha
  have before : (SourcePlan.treeLayout S p).forward≤GeometryStartup.outputBase (history S p) := by
    rw [GeometryStartup.outputBase_eq]
    exact (SourcePhase.forward_before S p).trans (Nat.le_add_right _ _)
  exact (m₁ address (Or.inl (ha.trans_le before))).trans (m₀ address ha)

#print axioms executes

theorem numeric {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val) :
    PositiveGraph.Metadata.Numeric (SourceGraph.Positive.width S p)
      (SourceGraph.Positive.dimension S p) (SourceGraph.Positive.count S p) t.val := by
  apply hs.numeric.transport
  intro i lo hi _
  apply hf.tapes i (Or.inr (by omega))
  have disjoint : Disjoint (Finset.Icc 140 159) work := by decide +kernel
  exact Finset.disjoint_left.mp disjoint (Finset.mem_Icc.mpr ⟨lo,hi⟩)

theorem retained {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val) :
    SourceGraph.Retain.Data S p t.val := by
  apply hs.data.transport
  intro i lo hi
  apply hf.tapes i (Or.inr (by omega))
  have disjoint : Disjoint (Finset.Icc 500 509) work := by decide +kernel
  exact Finset.disjoint_left.mp disjoint (Finset.mem_Icc.mpr ⟨lo,hi⟩)

theorem fresh {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val)
    (i : ℕ) (hi : 1261 ≤ i) : Blank t.val i := by
  apply RationalAccumulator.blank_of_eq (hf.tapes i (Or.inr (by omega)) ?_)
    ⟨0,hs.fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega))⟩
  have upper : ∀j∈work,j<1261 := by decide +kernel
  intro hin
  have bound:=upper i hin
  omega

#print axioms retained
#print axioms fresh
end Maxwell.Cost.RoutingPorts.Complete.SourceGeometry
