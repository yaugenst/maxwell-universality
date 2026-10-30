import Maxwell.Continuum.SourceRoutingTraversalExecution

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def loadedCode : Code := .seq (.call (WordTransfer.clone 810 830))
  (.seq (PhysicalMaterial.FixedSubtract.code 830 1) code)

theorem loaded_executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (depth : v 810=total)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State v heap rows total root 0 start s) (h830 : Blank s.val 830) :
    ∃steps t,Executes input tape loadedCode steps s t ∧
      steps ≤ cost heap rows total+44*total.bits.length+48 ∧
      State v heap rows total root (total-1) start t ∧ Blank t.val 830 := by
  have count : RationalAccumulator.Word s.val 810 total := by
    simpa only [values,depth] using hs.bank 810 (by decide)
  obtain ⟨origin,ho⟩:=count
  obtain ⟨co,hco⟩:=h830
  obtain ⟨a,ec,tt,tf⟩:=WordCall.clone 810 830 (by decide) input tape total.bits origin co s ho hco
  have cf : BinaryPrecision.Frame {830} s.val a.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠830 by simpa using hi)]
  have ha:=hs.clear cf
  have ca : RationalAccumulator.Word a.val 830 total := ⟨co,by simp only [tt,Function.update_self]⟩
  obtain ⟨cd,b,ed,hcd,cb,fd⟩:=PhysicalMaterial.FixedSubtract.executes 830 1 total setup.positive input tape a ca
  obtain ⟨steps,t,he,hcost,ht,zt⟩:=executes v heap rows total root setup input tape start b (ha.clear fd) cb
  refine ⟨(15*total.bits.length+17)+(cd+steps),t,ec.seq (ed.seq he),?_,ht,zt⟩
  dsimp only [PhysicalMaterial.FixedSubtract.costBound] at hcd
  omega

#print axioms loaded_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
