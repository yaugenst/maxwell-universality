import Maxwell.Continuum.SourceRoutingCountedGeometry
import Maxwell.Continuum.SourceRoutingSourceTreeCost
import Maxwell.Continuum.SourceRoutingHistoriesCost
import Maxwell.Continuum.SourceRoutingGeometryProducerCost

/-! The source-driven producer has cubic routing-size cost and fourth-power
word cost. Every term in the width envelope is a stored bit width, a logarithmic
routing depth, or an address bit width; no execution count is hidden in it. -/
namespace Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Logical Maxwell.Logical.Routing SourceGraph.Positive
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024

namespace SourceGeometry

def wordBound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  SourceTree.wordBound S p room+
    PhaseStartup.inputWidth (SourcePhase.half S p) (SourcePhase.layout S p).forward
      (SourcePhase.layout S p).backward+
    GeometryHistories.bound (SourcePhase.plan S p)+
    GeometryProducer.addressWidth (history S p) (backward S p)
      (GeometryEmission.capacity (SourcePhase.side S p) (GeometryProducer.vertices S p) (GeometryProducer.edges S p))

theorem side_power (S : Source.SparseSystem) (p : ℕ) : 2^SourcePlan.depth S p=SourcePhase.side S p := by
  unfold SourcePhase.side SourcePhase.half
  rw [←SourcePlan.half_indexed]
  simp only [SourcePlan.depth,SourcePlan.half,portHalfSide,pow_succ']

theorem cost_bound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    cost S p room≤2^704*(SourcePhase.side S p+1)^3*(wordBound S p room+10)^4 := by
  let q:=SourcePhase.side S p
  let W:=wordBound S p room+10
  let T:=(q+1)^3*W^4
  have positive : 1≤W:=by unfold W;omega
  have small : W^2≤T:=
    (Nat.pow_le_pow_right positive (by decide : (2:ℕ)≤4)).trans
      (Nat.le_mul_of_pos_left _ (by positivity))
  have quadratic (x : ℕ) (h : x+3≤W) : (x+3)^2≤T:=
    (Nat.pow_le_pow_left h 2).trans small
  have a:=SourceTree.cost_bound S p room
  rw [side_power] at a
  have tree : SourceTree.cost S p room≤2^702*T:=by
    apply a.trans
    calc
      _≤2^702*(q+1)^3*W^4:=Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by unfold W wordBound;omega) 4)
      _=2^702*T:=by dsimp only [T];ring
  have startup : PhaseStartup.cost (SourcePhase.half S p) (SourcePhase.layout S p).forward
      (SourcePhase.layout S p).backward≤2^200*T:=by
    have size:=quadratic (PhaseStartup.inputWidth (SourcePhase.half S p)
      (SourcePhase.layout S p).forward (SourcePhase.layout S p).backward) (by unfold W wordBound;omega)
    have size' : (PhaseStartup.inputWidth (SourcePhase.half S p)
        (SourcePhase.layout S p).forward (SourcePhase.layout S p).backward+2)^2≤T:=
      (Nat.pow_le_pow_left (by omega) 2).trans size
    change 3000*8^59*(PhaseStartup.inputWidth _ _ _+2)^2≤_
    exact (Nat.mul_le_mul_left _ size').trans (Nat.mul_le_mul_right _ (by norm_num))
  have array:=GeometryPhase.generateCost_polynomial (SourcePhase.plan S p)
  have phase : GeometryPhase.generateCost (SourcePhase.plan S p)≤2^116*T:=by
    apply array.trans
    calc
      _≤2^116*(q+1)^3*W^4:=by
        apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          have quadratic : q*q+1≤(q+1)^2:=by nlinarith only [Nat.zero_le q]
          exact quadratic.trans (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le q)) (by decide))
        · apply (Nat.pow_le_pow_left (show (SourcePhase.plan S p).bound+3≤W by
            unfold W wordBound GeometryHistories.bound;omega) 2).trans
          exact Nat.pow_le_pow_right positive (by decide)
      _=2^116*T:=by dsimp only [T];ring
  have generation:=GeometryHistories.generateCost_polynomial (SourcePhase.plan S p) (SourcePhase.sequential S p)
  have histories : GeometryHistories.generateCost (SourcePhase.plan S p)≤2^214*T:=by
    apply generation.trans
    calc
      _≤2^214*(q+1)^3*W^4:=by
        apply Nat.mul_le_mul_left
        apply (Nat.pow_le_pow_left (show GeometryHistories.bound (SourcePhase.plan S p)+3≤W by
          unfold W wordBound;omega) 2).trans
        exact Nat.pow_le_pow_right positive (by decide)
      _=2^214*T:=by dsimp only [T];ring
  have produced:=GeometryProducer.price_address_bound S p (history S p) (backward S p) (history_start S p)
  have geometry : GeometryProducer.price S p (history S p) (backward S p) (history_start S p)≤2^272*T:=by
    apply produced.trans
    calc
      _≤2^272*(q+1)^3*W^4:=by
        apply Nat.mul_le_mul_left
        apply (Nat.pow_le_pow_left (show GeometryProducer.addressWidth (history S p) (backward S p)
            (GeometryEmission.capacity q (GeometryProducer.vertices S p) (GeometryProducer.edges S p))+3≤W by
          unfold W wordBound q;omega) 2).trans
        exact Nat.pow_le_pow_right positive (by decide)
      _=2^272*T:=by dsimp only [T];ring
  unfold cost SourceHistories.cost SourcePhase.prepareCost GeometryHistories.fromArraysCost
  calc
    _≤2^704*T:=by omega
    _=2^704*(q+1)^3*W^4:=by dsimp only [T];ring

#print axioms cost_bound
end SourceGeometry

namespace CountedGeometry

def wordBound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  SourceGeometry.wordBound S p room+countWidth S p

theorem cost_bound (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) :
    cost S p room≤2^705*(SourcePhase.side S p+1)^3*(wordBound S p room+10)^4 := by
  let W:=wordBound S p room+10
  let T:=(SourcePhase.side S p+1)^3*W^4
  have a:=SourceGeometry.cost_bound S p room
  have geometry : SourceGeometry.cost S p room≤2^704*T:=by
    apply a.trans
    calc
      _≤2^704*(SourcePhase.side S p+1)^3*W^4:=Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by unfold W wordBound;omega) 4)
      _=2^704*T:=by dsimp only [T];ring
  have square : (countWidth S p+2)^2≤T:=by
    calc
      _≤W^2:=Nat.pow_le_pow_left (by unfold W wordBound;omega) 2
      _≤W^4:=Nat.pow_le_pow_right (by unfold W;omega) (by decide)
      _≤T:=Nat.le_mul_of_pos_left _ (by positivity)
  have counting:=Nat.mul_le_mul_left (2^130) square
  unfold cost
  calc
    _≤2^705*T:=by omega
    _=2^705*(SourcePhase.side S p+1)^3*W^4:=by dsimp only [T];ring

#print axioms cost_bound
end CountedGeometry
end Maxwell.Cost.RoutingPorts.Complete
