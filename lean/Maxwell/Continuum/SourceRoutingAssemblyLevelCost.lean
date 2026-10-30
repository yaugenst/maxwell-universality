import Maxwell.Continuum.SourceRoutingAssemblyLevelCompleted

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 512

def upperBodyCost (count B : ℕ) : ℕ := 2^120*(B+2)^2+
  2^45*(count+1)*(AssemblyDescriptor.wordBound B+2)^2+
  3000*8^2*(AssemblyDescriptor.wordBound B+2)^2
def upperCost (nodes count B : ℕ) : ℕ :=
  (nodes+1)*(13*B+15)+nodes*upperBodyCost count B+21*B+21+2^110*(B+2)^2

theorem wholeCost_bound {rows columns depth : ℕ} (p : Plan rows columns depth) (nodes count : ℕ)
    (hn : 2^depth ≤ nodes) (hc : 2*2^(columns+rows) ≤ count)
    (hb : (2^depth).bits.length ≤ uniformWidth p.L) :
    wholeCost p ≤ upperCost nodes count (uniformWidth p.L) := by
  let B:=uniformWidth p.L
  have body : bodyCost (columns+rows) B ≤ upperBodyCost count B := by
    have hh:=Nat.mul_le_mul_right ((AssemblyDescriptor.wordBound B+2)^2)
      (Nat.mul_le_mul_left (2^45) (Nat.add_le_add_right hc 1))
    dsimp only [bodyCost,upperBodyCost]
    omega
  have main:=Nat.mul_le_mul hn body
  have overhead:=Nat.mul_le_mul (Nat.add_le_add_right hn 1)
    (show 13*(2^depth).bits.length+15 ≤ 13*B+15 by omega)
  dsimp only [B] at main overhead
  dsimp only [wholeCost,cost,upperCost]
  omega

#print axioms wholeCost_bound
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
