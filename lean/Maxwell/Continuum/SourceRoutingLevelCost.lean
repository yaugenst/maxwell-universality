import Maxwell.Continuum.SourceRoutingLevelCompleted

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 512

def wholeCost {k : ℕ} (p : Plan k) : ℕ := cost p+15*p.nodes.bits.length+17+2^110*(p.B+2)^2
def upperCost (nodes count B : ℕ) : ℕ :=
  (nodes+1)*(13*B+15)+nodes*(2^300*(count+1)*(B+2)^3)+21*B+21+2^110*(B+2)^2

theorem wholeCost_bound {k : ℕ} (p : Plan k) (nodes count : ℕ)
    (hn : p.nodes ≤ nodes) (hc : 2*2^k ≤ count) (hb : p.nodes.bits.length ≤ p.B) :
    wholeCost p ≤ upperCost nodes count p.B := by
  have main:=Nat.mul_le_mul hn
    (Nat.mul_le_mul_right ((p.B+2)^3) (Nat.mul_le_mul_left (2^300) (Nat.add_le_add_right hc 1)))
  have overhead:=Nat.mul_le_mul (Nat.add_le_add_right hn 1)
    (show 13*p.nodes.bits.length+15 ≤ 13*p.B+15 by omega)
  dsimp only [wholeCost,cost,bodyCost,upperCost]
  omega

#print axioms wholeCost_bound
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
