import Maxwell.Continuum.SourceRoutingSourcePhaseWorkspace
import Maxwell.Continuum.SourceRoutingSourcePhaseInverse
import Maxwell.Continuum.SourceRoutingHistoriesComplete
import Maxwell.Cost.ArrayPrefix

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

structure Prepared (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  bank : NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed (plan S p) 0) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  metadata : GeometryPhase.Metadata (plan S p) s.val
  count : Word s.val 709 (side S p*side S p)
  innerBlank : Blank s.val 1240
  outerBlank : Blank s.val 1241
  targets : BitArray.Represents s.val.memory ((plan S p).base 0) (plan S p).width
    (IncidenceEncoding.words (plan S p).width
      (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target))
  labels : BitArray.Represents s.val.memory ((plan S p).base 1) (plan S p).width
    (IncidenceEncoding.words (plan S p).width
      (GeometryPhase.labels (Composition.SourceRouting.indexedData S p).colors))
  inverse : BitArray.Represents s.val.memory (layout S p).backward (plan S p).width
    (IncidenceEncoding.words (plan S p).width
      (GeometryPhase.targets (Composition.SourceRouting.indexedData S p).target.symm))
  backwardWord : Word s.val 717 (layout S p).backward

def prepareCode : Code := .seq SourceTree.code PhaseStartup.code
def prepareWork : Finset ℕ := SourceTree.work∪PhaseStartup.work
def prepareCost (S : Source.SparseSystem) (p : ℕ)
    (room : SourceGraph.Positive.dimension S p<2^SourceGraph.Positive.width S p) : ℕ :=
  SourceTree.cost S p room+PhaseStartup.cost (half S p) (layout S p).forward (layout S p).backward

theorem prepare_executes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape prepareCode steps s t ∧ steps≤prepareCost S p hs.room ∧
      Prepared S p t ∧ ArchiveFrame prepareWork s.val t.val ∧
      (∀address,address<(SourcePlan.treeLayout S p).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c0,a,e0,h0,labels,clean,_a839,_a831,_a830,f0,metadataA,quotient,stored,memoryBefore,halfWord⟩:=
    SourceTree.executes S p hm input tape s hs
  have fresh : ∀i∈GeometryArithmetic.ids,Blank a.val i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact tree_fresh hs f0 i (Finset.mem_Icc.mp hi).1
    · exact quotient i hi
  have halfWord' : Word a.val 710 (half S p) := by
    simpa only [SourcePlan.half_indexed,half] using halfWord
  obtain ⟨c1,t,e1,h1,bank,ready,metadataT,count,f1⟩:=PhaseStartup.executes (half S p)
    (half_pos S p) (layout S p) (ordered S p) input tape a
    (metadata S p a.val metadataA) halfWord' fresh (tree_ready clean)
  have blank (i : ℕ) (hi : i=1240 ∨ i=1241 ∨ i=1249) : Blank t.val i := by
    apply RationalAccumulator.blank_of_eq (f1.tapes i ?_) (tree_fresh hs f0 i (by omega))
    rcases hi with rfl|rfl|rfl <;> decide
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,
    ⟨bank,ready,blank 1249 (by decide),metadataT,count,blank 1240 (by decide),blank 1241 (by decide),?_,?_,?_,
      RationalAccumulator.word_of_eq (f1.tapes 717 (by decide)) metadataA.backward⟩,
    (f0.mono Finset.subset_union_left).trans ((ArchiveFrame.of_binary f1).mono Finset.subset_union_right),?_⟩
  · rw [f1.memory];exact target_stored S p a.val stored
  · rw [f1.memory];exact labels_stored S p a.val.memory labels
  · rw [f1.memory];exact backward_stored S p a.val stored
  · intro address ha
    rw [f1.memory]
    exact memoryBefore address ha

#print axioms prepare_executes
end Maxwell.Cost.RoutingPorts.Complete.SourcePhase
