import Maxwell.Continuum.SourceRoutingLevelExecution

/-! The routing loop loads its own countdown from the stored level size;
the copy and the eventual counter cleanup are included in execution cost. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def loadedCode : Code := .seq (.call (WordTransfer.clone 813 831)) code

theorem loaded_executes {k : ℕ} (p : Plan k) (hn : p.initial 813=p.nodes)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State p 0 start s) (h831 : Blank s.val 831) :
    ∃steps t, Executes input tape loadedCode steps s t ∧
      steps ≤ cost p+15*p.nodes.bits.length+17 ∧ State p p.nodes start t ∧ Blank t.val 831 := by
  have count : RationalAccumulator.Word s.val 813 p.nodes := by
    simpa only [values,Function.iterate_zero,Function.id_def,hn] using hs.bank 813 (by decide)
  obtain ⟨origin,ho⟩:=count
  obtain ⟨co,hco⟩:=h831
  obtain ⟨a,ec,tt,tf⟩:=WordCall.clone 813 831 (by decide) input tape p.nodes.bits origin co s ho hco
  have cf : BinaryPrecision.Frame {831} s.val a.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠831 by simpa using hi)]
  have ha:=hs.clear cf
  have ca : RationalAccumulator.Word a.val 831 p.nodes := ⟨co,by simp only [tt,Function.update_self]⟩
  obtain ⟨steps,t,he,hcost,ht,zt⟩:=executes p input tape start a ha ca
  exact ⟨(15*p.nodes.bits.length+17)+steps,t,ec.seq he,by omega,ht,zt⟩

#print axioms loaded_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
