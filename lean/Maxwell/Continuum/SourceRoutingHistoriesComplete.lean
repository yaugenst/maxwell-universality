import Maxwell.Continuum.SourceRoutingHistoriesGenerate

/-! The complete three-phase history producer starts with the computed
permutation and color arrays. Its output space uses its actual initial memory;
no precomputed history or zero-filled allocation is an input. -/

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def fromArraysCode : Code := .seq GeometryPhase.generateCode generateCode
def fromArraysCost {q : ℕ} (p : GeometryPhase.Plan q) : ℕ :=
  GeometryPhase.generateCost p+generateCost p
def fromArraysWork : Finset ℕ := GeometryPhase.loopWork∪GeometryHistory.loopWork

def initialArrays {q : ℕ} (p : GeometryPhase.Plan q) (memory : ℕ→Bool) :
    Fin 3→Vector (List Bool) (q*q) :=
  fun slot=>GeometryArray.snapshot memory (p.base ⟨slot.val+2,by omega⟩) p.width (q*q)

theorem initial_runtime {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q)
    (colors : RowColoring target) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed p 0) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometryPhase.Metadata p s.val)
    (targets : BitArray.Represents s.val.memory (p.base 0) p.width
      (IncidenceEncoding.words p.width (GeometryPhase.targets target)))
    (labels : BitArray.Represents s.val.memory (p.base 1) p.width
      (IncidenceEncoding.words p.width (GeometryPhase.labels colors))) :
    GeometryPhase.Runtime p colors (initialArrays p s.val.memory) 0 s := by
  refine ⟨Nat.zero_le _,bank,ready,privateBlank,metadata,?_⟩
  intro slot
  fin_cases slot
  · exact targets
  · exact labels
  all_goals exact GeometryArray.snapshot_represents _ _ _ _

theorem from_arrays_executes {q : ℕ} {target : Equiv.Perm (Port q)} (p : GeometryPhase.Plan q)
    (sequential : Sequential p)
    (baseOrder : ∀slot : Fin 5,2≤slot.val→p.base 2≤p.base slot)
    (colors : RowColoring target) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometryPhase.seed p 0) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometryPhase.Metadata p s.val) (count : Word s.val 709 (q*q))
    (innerBlank : Blank s.val 1240) (outerBlank : Blank s.val 1241)
    (targets : BitArray.Represents s.val.memory (p.base 0) p.width
      (IncidenceEncoding.words p.width (GeometryPhase.targets target)))
    (labels : BitArray.Represents s.val.memory (p.base 1) p.width
      (IncidenceEncoding.words p.width (GeometryPhase.labels colors))) :
    ∃steps t,Executes input tape fromArraysCode steps s t ∧ steps≤fromArraysCost p ∧
      GeometryHistory.Runtime (historyPlan p 2) (keys colors 2) (2*q) t ∧ Blank t.val 1241 ∧
      Stored p colors t.val.memory ∧ ArchiveFrame fromArraysWork s.val t.val ∧
      (∀address,address<p.base 2→t.val.memory address=s.val.memory address) := by
  obtain ⟨c0,a,e0,h0,ra,a1240,arrays,f0,m0⟩:=GeometryPhase.generate_arrays p colors
    (initialArrays p s.val.memory) input tape s
    (initial_runtime p colors s bank ready privateBlank metadata targets labels) count innerBlank
  obtain ⟨c1,t,e1,h1,rt,t1241,stored,f1,m1⟩:=generate_executes p sequential colors input tape a
    ra.bank ra.ready ra.privateBlank ra.metadata
    (RationalAccumulator.word_of_eq (f0.tapes 709 (by omega) (by decide +kernel)) count) a1240
    (RationalAccumulator.blank_of_eq (f0.tapes 1241 (by omega) (by decide +kernel)) outerBlank)
    (phase_key p colors a.val.memory arrays)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,rt,t1241,stored,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right),?_⟩
  intro address ha
  have phaseOutside : ∀slot : Fin 5,2≤slot.val→address<p.base slot ∨
      p.base slot+q*q*p.width≤address := fun slot hs=>Or.inl (ha.trans_le (baseOrder slot hs))
  have historyOutside : ∀slot : Fin 3,address<(historyPlan p slot).slab 1 ∨
      (historyPlan p slot).slab 1+2*q*(historyPlan p slot).stride≤address := by
    intro slot
    left
    have hh:=ha.trans_le (baseOrder ⟨slot.val+2,by omega⟩ (by change 2≤slot.val+2;omega))
    exact hh.trans_le (Nat.le_add_right _ _)
  exact (m1 address historyOutside).trans (m0 address phaseOutside)

#print axioms from_arrays_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistories
