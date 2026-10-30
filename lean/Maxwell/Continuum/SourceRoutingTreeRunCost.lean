import Maxwell.Continuum.SourceRoutingTreeCost

/-! Source-independent polynomial charges for the two actual tree traversals. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 1024

def runWidth (heap rows total : ℕ) : ℕ :=
  ControllerWidth.baseWidth heap (2^(total+rows)) (total+rows+1) total

theorem forward_width_bound (heap rows total : ℕ) :
    Traversal.width heap rows total+2 ≤ 2^31*(runWidth heap rows total+2) := by
  dsimp only [Traversal.width,Level.uniformWidth,runWidth]
  omega

theorem forward_level_width_bound (heap rows total : ℕ) :
    Level.uniformWidth (Traversal.width heap rows total)+2 ≤ 2^62*(runWidth heap rows total+2) := by
  dsimp only [Traversal.width,Level.uniformWidth,runWidth]
  omega

theorem reverse_level_width_bound (heap rows total : ℕ) :
    AssemblyLevel.uniformWidth (AssemblyTraversal.width heap rows total)+2 ≤
      2^83*(runWidth heap rows total+2) := by
  dsimp only [AssemblyTraversal.width,AssemblyLevel.uniformWidth,AssemblyTraversal.baseWidth,runWidth]
  omega

def runVolume (heap rows total : ℕ) : ℕ :=
  (2^total+1)*(2^(total+rows)+1)*(runWidth heap rows total+2)^3

theorem Traversal.bodyCost_polynomial (heap rows total : ℕ) :
    Traversal.bodyCost heap rows total ≤ 2^500*runVolume heap rows total := by
  calc
    _ ≤ 2^310*(2^total+1)*(2^(total+rows)+1)*
        (Level.uniformWidth (Traversal.width heap rows total)+2)^3 := Level.upperCost_polynomial _ _ _
    _ ≤ 2^310*(2^total+1)*(2^(total+rows)+1)*
        (2^62*(runWidth heap rows total+2))^3 := by gcongr;exact forward_level_width_bound _ _ _
    _ = (2^310*(2^62)^3)*runVolume heap rows total := by dsimp only [runVolume];ring
    _ ≤ 2^500*runVolume heap rows total := Nat.mul_le_mul_right _ (by norm_num)

theorem AssemblyTraversal.bodyCost_polynomial (heap rows total : ℕ) :
    AssemblyTraversal.bodyCost heap rows total ≤ 2^500*runVolume heap rows total := by
  calc
    _ ≤ 2^180*(2^total+1)*(2^(total+rows)+1)*
        (AssemblyLevel.uniformWidth (AssemblyTraversal.width heap rows total)+2)^3 :=
      AssemblyLevel.upperCost_polynomial _ _ _
    _ ≤ 2^180*(2^total+1)*(2^(total+rows)+1)*
        (2^83*(runWidth heap rows total+2))^3 := by gcongr;exact reverse_level_width_bound _ _ _
    _ = (2^180*(2^83)^3)*runVolume heap rows total := by dsimp only [runVolume];ring
    _ ≤ 2^500*runVolume heap rows total := Nat.mul_le_mul_right _ (by norm_num)

theorem runVolume_one (heap rows total : ℕ) : 1 ≤ runVolume heap rows total := by
  dsimp only [runVolume]
  exact Nat.succ_le_of_lt (by positivity)

theorem runVolume_depth (heap rows total : ℕ) : total+1 ≤ runVolume heap rows total := by
  have hh : total+1 ≤ (2 : ℕ)^total := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hq : 2^total+1 ≤ runVolume heap rows total := by
    dsimp only [runVolume]
    exact (Nat.le_mul_of_pos_right _ (by positivity)).trans (Nat.le_mul_of_pos_right _ (by positivity))
  omega

theorem Traversal.cost_polynomial (heap rows total : ℕ) :
    Traversal.cost heap rows total ≤ 2^505*(total+1)*runVolume heap rows total := by
  let M:=runVolume heap rows total
  have hd : total+1 ≤ M := runVolume_depth _ _ _
  have hb : (total-1).bits.length ≤ M := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (by omega)
  have main:=Nat.mul_le_mul_left (total-1) (Traversal.bodyCost_polynomial heap rows total)
  have main' : (total-1)*Traversal.bodyCost heap rows total ≤ 2^500*(total+1)*M := by
    calc
      _ ≤ (total-1)*(2^500*M) := main
      _ ≤ (total+1)*(2^500*M) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have overhead : total*(13*(total-1).bits.length+15) ≤ 28*(total+1)*M := by
    have h1 : 1 ≤ M := runVolume_one _ _ _
    calc
      _ ≤ (total+1)*(28*M) := by gcongr <;> omega
      _ = _ := by ring
  have rest : 6*(total-1).bits.length+4 ≤ 10*(total+1)*M := by
    have h1 : 1 ≤ M := runVolume_one _ _ _
    have hm : M ≤ (total+1)*M := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [hb,h1,hm]
  dsimp only [Traversal.cost]
  change _ ≤ 2^505*(total+1)*M
  nlinarith only [main',overhead,rest]

theorem AssemblyTraversal.cost_polynomial (heap rows total : ℕ) :
    AssemblyTraversal.cost heap rows total ≤ 2^505*(total+1)*runVolume heap rows total := by
  let M:=runVolume heap rows total
  have hd : total+1 ≤ M := runVolume_depth _ _ _
  have hb : total.bits.length ≤ M := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (by omega)
  have main:=Nat.mul_le_mul_left total (AssemblyTraversal.bodyCost_polynomial heap rows total)
  have main' : total*AssemblyTraversal.bodyCost heap rows total ≤ 2^500*(total+1)*M := by
    calc
      _ ≤ total*(2^500*M) := main
      _ ≤ (total+1)*(2^500*M) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have overhead : (total+1)*(13*total.bits.length+15) ≤ 28*(total+1)*M := by
    have h1 : 1 ≤ M := runVolume_one _ _ _
    calc
      _ ≤ (total+1)*(28*M) := by gcongr;omega
      _ = _ := by ring
  have rest : 6*total.bits.length+4 ≤ 10*(total+1)*M := by
    have h1 : 1 ≤ M := runVolume_one _ _ _
    have hm : M ≤ (total+1)*M := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [hb,h1,hm]
  dsimp only [AssemblyTraversal.cost]
  change _ ≤ 2^505*(total+1)*M
  nlinarith only [main',overhead,rest]

#print axioms Traversal.cost_polynomial
#print axioms AssemblyTraversal.cost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.Tree
