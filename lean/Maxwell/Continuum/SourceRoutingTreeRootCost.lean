import Maxwell.Continuum.SourceRoutingTreeRunCost

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 1024

theorem runVolume_width (heap rows total : ℕ) :
    (runWidth heap rows total+2)^3 ≤ runVolume heap rows total := by
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem runVolume_count (heap rows total : ℕ) :
    (2^(total+rows)+1)*(runWidth heap rows total+2)^3 ≤ runVolume heap rows total := by
  have h : 1 ≤ (2 : ℕ)^total+1 := Nat.le_add_left _ _
  simpa only [runVolume,one_mul,mul_assoc] using
    Nat.mul_le_mul_right ((2^(total+rows)+1)*(runWidth heap rows total+2)^3) h

theorem RootRun.cost_polynomial (heap rows total : ℕ) :
    RootRun.cost heap rows total ≤ 2^520*(total+1)*runVolume heap rows total := by
  let M:=runVolume heap rows total
  let L:=runWidth heap rows total
  have width:=forward_width_bound heap rows total
  have square : (Traversal.width heap rows total+2)^2 ≤ 2^62*(L+2)^2 := by
    calc
      _ ≤ (2^31*(L+2))^2 := Nat.pow_le_pow_left width 2
      _ = _ := by ring
  have cube : (Traversal.width heap rows total+2)^3 ≤ 2^93*(L+2)^3 := by
    calc
      _ ≤ (2^31*(L+2))^3 := Nat.pow_le_pow_left width 3
      _ = _ := by ring
  have sq3 : (L+2)^2 ≤ (L+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have m3 : (L+2)^3 ≤ M := runVolume_width _ _ _
  have sqM : (Traversal.width heap rows total+2)^2 ≤ 2^62*M :=
    square.trans (Nat.mul_le_mul_left _ (sq3.trans m3))
  have rootTerm : 2^180*(2^(total+rows)+1)*(Traversal.width heap rows total+2)^3 ≤ 2^300*M := by
    calc
      _ ≤ 2^180*(2^(total+rows)+1)*(2^93*(L+2)^3) := Nat.mul_le_mul_left _ cube
      _ = (2^180*2^93)*((2^(total+rows)+1)*(L+2)^3) := by ring
      _ ≤ (2^180*2^93)*M := Nat.mul_le_mul_left _ (runVolume_count _ _ _)
      _ ≤ 2^300*M := Nat.mul_le_mul_right _ (by norm_num)
  have stepTerm : 2^110*(Traversal.width heap rows total+2)^2 ≤ 2^200*M := by
    calc
      _ ≤ 2^110*(2^62*M) := Nat.mul_le_mul_left _ sqM
      _ = (2^110*2^62)*M := by ring
      _ ≤ 2^200*M := Nat.mul_le_mul_right _ (by norm_num)
  have reverseTerm : 2^102*(Traversal.width heap rows total+2)^2 ≤ 2^200*M := by
    calc
      _ ≤ 2^102*(2^62*M) := Nat.mul_le_mul_left _ sqM
      _ = (2^102*2^62)*M := by ring
      _ ≤ 2^200*M := Nat.mul_le_mul_right _ (by norm_num)
  have first:=Traversal.cost_polynomial heap rows total
  have last:=AssemblyTraversal.cost_polynomial heap rows total
  have hb : total.bits.length ≤ M := (natural_bits_length_le total).trans (by
    have h:=runVolume_depth heap rows total;omega)
  have h1 : 1 ≤ M := runVolume_one _ _ _
  have hm : M ≤ (total+1)*M := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [RootRun.cost,RoundTrip.cost]
  change _ ≤ 2^520*(total+1)*M
  nlinarith only [rootTerm,stepTerm,reverseTerm,first,last,hb,h1,hm]

#print axioms RootRun.cost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.Tree
