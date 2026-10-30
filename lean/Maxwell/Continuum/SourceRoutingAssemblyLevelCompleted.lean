import Maxwell.Continuum.SourceRoutingAssemblyLevelExecution
import Maxwell.Continuum.SourceRoutingAssemblyAdvanceValues
import Maxwell.Continuum.SourceRoutingLevelCompleted

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def nextCode : Code := .seq loadedCode AssemblyAdvance.code
def nextValues (v : ℕ→ℕ) (nodes : ℕ) : ℕ→ℕ := AssemblyAdvance.output (values v nodes)
def wholeCost {rows columns depth : ℕ} (p : Plan rows columns depth) : ℕ :=
  cost p+15*(2^depth).bits.length+17+2^110*(uniformWidth p.L+2)^2

theorem State.initial {rows columns depth : ℕ} (p : Plan rows columns depth) (s : Store)
    (hb : NatAssign.Bank Division.ids p.initial s.val) (hz : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (hi : p.Inputs 0 s.val.memory) : State p 0 s.val s :=
  ⟨hb,hz,h839,hi,fun _ h => by omega,Level.Frame.refl _,Memory.Frame.refl _ _ _⟩

theorem next_executes {rows columns depth : ℕ} (p : Plan rows columns depth)
    (hn : p.initial 813=2^depth) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank Division.ids p.initial s.val) (hz : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (h831 : Blank s.val 831) (hi : p.Inputs 0 s.val.memory) :
    ∃steps t,Executes input tape nextCode steps s t ∧ steps ≤ wholeCost p ∧
      NatAssign.Bank Division.ids (nextValues p.initial (2^depth)) t.val ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ Blank t.val 831 ∧
      p.Done (2^depth) t.val.memory ∧ Level.Frame s.val t.val ∧
      Memory.Frame (block p.heap p.rootCount p.rootWidth (2^depth-1))
        (2^depth*stride p.rootCount p.rootWidth) s.val.memory t.val.memory := by
  obtain ⟨c0,a,e0,h0,sa,a831⟩:=loaded_executes p hn input tape s.val s (State.initial p s hb hz h839 hi) h831
  have coords:=coordinates p.initial p.heap p.rootCount p.rootWidth depth (columns+rows) p.coordinates (2^depth)
  have words:=values_simple_width p.initial (2^depth) p.L p.L_lower p.words p.nodes_width
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values p.initial (2^depth) j=0 := by
    intro j hj
    have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts writes := by decide
    rw [values_other p.initial (2^depth) j (Finset.disjoint_left.mp disjoint hj)]
    exact p.zero j hj
  obtain ⟨c1,t,e1,h1,b1,z1,t839,f1⟩:=AssemblyAdvance.executes (values p.initial (2^depth)) (uniformWidth p.L)
    (by dsimp only [uniformWidth];omega) coords.two zero words input tape a sa.bank sa.clean sa.scratch
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,t839,
    RationalAccumulator.blank_of_eq (f1.tapes 831 (by decide)) a831,?_,
    sa.frame.trans (Level.Frame.of_arithmetic f1),?_⟩
  · dsimp only [wholeCost];omega
  · simpa only [f1.memory] using sa.done
  · simpa only [f1.memory] using sa.memory

#print axioms next_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
