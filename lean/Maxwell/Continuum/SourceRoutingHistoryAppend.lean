import Maxwell.Continuum.SourceRoutingHistoryRestart

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def appendCode : Code := .seq (NatAssign.code restart) generateCode
def appendCost {q : ℕ} (p : Plan q) : ℕ := 2^40*(p.bound+3)^2+generateCost p.following

theorem append_executes {q : ℕ} (p : Plan q) (previous next : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width next) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : Runtime p previous (2*q) s) (blank : Blank s.val 1241)
    (initialNext : BitArray.Represents s.val.memory p.following.base p.width (IncidenceEncoding.words p.width next)) :
    ∃steps t,Executes input tape appendCode steps s t ∧ steps ≤ appendCost p ∧
      Runtime p.following next (2*q) t ∧ Blank t.val 1241 ∧
      ArchiveFrame loopWork s.val t.val ∧ MemoryFrame p.following s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=restart_executes p input tape s state.bank state.ready state.privateBlank
  have ma:=state.metadata.frame (ArchiveFrame.of_binary f0) (by decide)
  have start : Runtime p.following next 0 a := by
    refine ⟨Nat.zero_le _,ba,za,a1249,
      RationalAccumulator.blank_of_eq (f0.tapes 1240 (by decide)) state.counterBlank,
      RationalAccumulator.word_of_eq (f0.tapes 709 (by decide)) state.count,⟨ma.width,ma.clock⟩,?_⟩
    intro j hj
    have hz : j=0 := by omega
    subst j
    simpa only [f0.memory,Plan.slab,Plan.width,Nat.zero_mul,Nat.add_zero,SortArrays.run] using initialNext
  obtain ⟨c1,t,e1,h1,rt,t1241,f1,m1⟩:=generate_executes p.following next fit input tape a start
    (RationalAccumulator.blank_of_eq (f0.tapes 1241 (by decide)) blank)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,rt,t1241,
    ((ArchiveFrame.of_binary f0).mono ?_).trans f1,?_⟩
  · intro j hj
    exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ hj))
  · simpa only [f0.memory] using m1

theorem earlier_slab_separated {q j : ℕ} (p : Plan q) (hj : j ≤ 2*q) :
    IncidenceEncoding.Separated (p.slab j) (q*q*p.width) (p.following.slab 1) (2*q*p.following.stride) := by
  left
  change p.slab j+p.stride ≤ p.following.slab 1
  have h:=p.slab_mono (show j+1 ≤ 2*q+1 by omega)
  have endPoint : p.slab j+p.stride=p.slab (j+1) := by dsimp only [Plan.slab];ring
  have nextBase : p.following.base ≤ p.following.slab 1 := Nat.le_add_right _ _
  rw [endPoint]
  exact h.trans nextBase

theorem earlier_stored {q : ℕ} {p : Plan q} {previous : SortArrays.Keys q} {before after : ℕ→Bool}
    (stored : Stored p previous (2*q) before) (frame : MemoryFrame p.following before after) :
    Stored p previous (2*q) after := by
  intro j hj
  exact frame.represents (earlier_slab_separated p hj) (stored j hj)

#print axioms append_executes
#print axioms earlier_stored
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
