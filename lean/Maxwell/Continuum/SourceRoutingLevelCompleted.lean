import Maxwell.Continuum.SourceRoutingLevelLoaded
import Maxwell.Continuum.SourceRoutingLevelHandoff
import Maxwell.Continuum.SourceRoutingLevelAdvanceValues

/-! The complete outer-loop body loads and executes its entire node
level, clears the inner counter, and computes the next level controls. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def nextCode : Code := .seq loadedCode Advance.code
def nextValues (v : ℕ→ℕ) (nodes : ℕ) : ℕ→ℕ := Advance.output (values v nodes)

theorem Frame.of_arithmetic {s t : BitRAMState} (hf : BinaryPrecision.Frame Division.work s t) : Frame s t :=
  ⟨hf.inputHead,hf.randomCursor,hf.output,fun i _ _ hi _ _ => hf.tapes i hi⟩

theorem next_executes (rows columns d heap rootCount rootWidth L : ℕ) (v : ℕ→ℕ)
    (target : Fin (2^(d+1))→Targets.Target rows (columns+1))
    (hL : 1 ≤ L) (hn : 2*(2*2^(columns+rows)) ≤ rootCount) (hw : columns+rows+3 ≤ rootWidth)
    (hs : Coordinates.Stored v heap rootCount rootWidth (d+1)
      (2*2^(columns+rows)) (columns+rows+2) 0)
    (hz : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (hv : ∀j∈Division.ids,(v j).bits.length ≤ L) (hp : (2^(d+1)).bits.length ≤ L)
    (hnodes : v 813=2^(d+1))
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (h831 : Blank s.val 831)
    (hi : (ofCoordinates rows columns d heap rootCount rootWidth L v target hL hn hw hs hz hv hp).Inputs s.val.memory) :
    let p:=ofCoordinates rows columns d heap rootCount rootWidth L v target hL hn hw hs hz hv hp
    ∃steps t,Executes input tape nextCode steps s t ∧
      steps ≤ cost p+15*p.nodes.bits.length+17+2^110*(p.B+2)^2 ∧
      NatAssign.Bank Division.ids (nextValues v p.nodes) t.val ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ Blank t.val 831 ∧
      p.Done p.nodes t.val.memory ∧ Frame s.val t.val ∧
      Memory.Frame (block heap rootCount rootWidth p.first) (p.nodes*stride rootCount rootWidth)
        s.val.memory t.val.memory := by
  dsimp only
  let p:=ofCoordinates rows columns d heap rootCount rootWidth L v target hL hn hw hs hz hv hp
  obtain ⟨c0,a,e0,h0,sa,a831⟩:=loaded_executes p hnodes input tape s.val s
    (State.initial p s hb hc h839 hi) h831
  have hc0:=coordinates_values v heap rootCount rootWidth (d+1) _ _ hs p.nodes
  have words:=values_width v p.nodes L hL hv hp
  have zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,values v p.nodes j=0 := by
    intro j hj;rw [quotient_values v p.nodes j hj];exact hz j hj
  obtain ⟨c1,t,e1,h1,b1,z1,t839,f1⟩:=Advance.executes (values v p.nodes) (uniformWidth L)
    zero hc0.two (by rw [hc0.width];omega) words input tape a sa.bank sa.clean sa.scratch
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,z1,t839,
    RationalAccumulator.blank_of_eq (f1.tapes 831 (by decide)) a831,?_,
    sa.frame.trans (Frame.of_arithmetic f1),?_⟩
  · change c0+c1 ≤ cost p+15*p.nodes.bits.length+17+2^110*(uniformWidth L+2)^2
    omega
  · simpa only [f1.memory] using sa.done
  · rw [f1.memory]
    exact sa.memory

#print axioms next_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
