import Maxwell.Continuum.SourceRoutingTreeComplete

/-! Polynomial charges for the actual routing-tree program. Large fixed
coefficients are handled algebraically, independently of the input. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 1024

theorem Level.upperCost_polynomial (nodes count B : ℕ) :
    Level.upperCost nodes count B ≤ 2^310*(nodes+1)*(count+1)*(B+2)^3 := by
  let M:=(nodes+1)*(count+1)*(B+2)^3
  have power : B+2 ≤ (B+2)^3 := le_self_pow₀ (by omega) (by decide : (3 : ℕ)≠0)
  have square : (B+2)^2 ≤ (B+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have factors : nodes+1 ≤ (nodes+1)*(count+1) := Nat.le_mul_of_pos_right _ (by omega)
  have base : (B+2)^3 ≤ M := Nat.le_mul_of_pos_left _ (by positivity)
  have overhead : (nodes+1)*(13*B+15) ≤ 28*M := by
    calc
      _ ≤ (nodes+1)*(28*(B+2)^3) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ ((nodes+1)*(count+1))*(28*(B+2)^3) := Nat.mul_le_mul_right _ factors
      _ = _ := by dsimp only [M];ring
  have main : nodes*(2^300*(count+1)*(B+2)^3) ≤ 2^300*M := by
    calc
      _ ≤ (nodes+1)*(2^300*(count+1)*(B+2)^3) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by dsimp only [M];ring
  have advance : 2^110*(B+2)^2 ≤ 2^110*M := Nat.mul_le_mul_left _ (square.trans base)
  have rest : 21*B+21 ≤ 42*M := by omega
  change (nodes+1)*(13*B+15)+nodes*(2^300*(count+1)*(B+2)^3)+21*B+21+2^110*(B+2)^2 ≤ _
  dsimp only [M] at overhead main advance rest
  nlinarith only [overhead,main,advance,rest]

theorem AssemblyLevel.upperBodyCost_polynomial (count B : ℕ) :
    AssemblyLevel.upperBodyCost count B ≤ 2^160*(count+1)*(B+2)^2 := by
  have width : AssemblyDescriptor.wordBound B+2 ≤ 2^36*(B+2) := by
    dsimp only [AssemblyDescriptor.wordBound]
    omega
  have square : (AssemblyDescriptor.wordBound B+2)^2 ≤ 2^72*(B+2)^2 := by
    calc
      _ ≤ (2^36*(B+2))^2 := Nat.pow_le_pow_left width 2
      _ = _ := by ring
  have base : (B+2)^2 ≤ (count+1)*(B+2)^2 := Nat.le_mul_of_pos_left _ (by omega)
  have a:=Nat.mul_le_mul_left (2^120) base
  have b:=Nat.mul_le_mul_left (2^45*(count+1)) square
  have c:=Nat.mul_le_mul_left (3000*8^2) (square.trans (Nat.mul_le_mul_left (2^72) base))
  dsimp only [AssemblyLevel.upperBodyCost]
  nlinarith only [a,b,c]

theorem AssemblyLevel.upperCost_polynomial (nodes count B : ℕ) :
    AssemblyLevel.upperCost nodes count B ≤ 2^180*(nodes+1)*(count+1)*(B+2)^3 := by
  let M:=(nodes+1)*(count+1)*(B+2)^3
  have power : B+2 ≤ (B+2)^3 := le_self_pow₀ (by omega) (by decide : (3 : ℕ)≠0)
  have square : (B+2)^2 ≤ (B+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have factors : nodes+1 ≤ (nodes+1)*(count+1) := Nat.le_mul_of_pos_right _ (by omega)
  have base : (B+2)^3 ≤ M := Nat.le_mul_of_pos_left _ (by positivity)
  have overhead : (nodes+1)*(13*B+15) ≤ 28*M := by
    calc
      _ ≤ (nodes+1)*(28*(B+2)^3) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ ((nodes+1)*(count+1))*(28*(B+2)^3) := Nat.mul_le_mul_right _ factors
      _ = _ := by dsimp only [M];ring
  have main : nodes*AssemblyLevel.upperBodyCost count B ≤ 2^160*M := by
    calc
      _ ≤ (nodes+1)*(2^160*(count+1)*(B+2)^2) :=
        Nat.mul_le_mul (by omega) (AssemblyLevel.upperBodyCost_polynomial count B)
      _ ≤ (nodes+1)*(2^160*(count+1)*(B+2)^3) := by gcongr
      _ = _ := by dsimp only [M];ring
  have advance : 2^110*(B+2)^2 ≤ 2^110*M := Nat.mul_le_mul_left _ (square.trans base)
  have rest : 21*B+21 ≤ 42*M := by omega
  dsimp only [AssemblyLevel.upperCost]
  dsimp only [M] at overhead main advance rest
  nlinarith only [overhead,main,advance,rest]

#print axioms Level.upperCost_polynomial
#print axioms AssemblyLevel.upperCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.Tree
