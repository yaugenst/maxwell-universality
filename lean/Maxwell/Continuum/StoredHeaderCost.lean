import Maxwell.Continuum.StoredHeaderRelocated
import Maxwell.Cost.RationalCanonical.StoredEmissionBounds

/-! The fixed header plan and canonical fraction reduction have cubic
runtime in the actual retained operand width, including relocation. -/
namespace Maxwell.Continuum.StoredHeader
open Maxwell.Cost
set_option maxHeartbeats 1500000

theorem emissionCost_cubic (B : ℕ) : emissionCost B 0 0+1 ≤ 2^140*(B+2)^3 := by
  have width : emissionWidth B ≤ 2^32*(B+2) := by
    unfold emissionWidth prepareWidth
    have length : plan.length=31 := by decide
    rw [length]
    omega
  have workspace : workspaceWidth B 0=emissionWidth B+1 := by
    simp [workspaceWidth]
  have cube : (2*emissionWidth B+5)^3 ≤ (2^35*(B+2))^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have canonical := RationalCanonical.StoredEmission.costBound_cubic
    (emissionWidth B) (workspaceWidth B 0)
  rw [workspace] at canonical
  have arg : emissionWidth B+(emissionWidth B+1)+4=2*emissionWidth B+5 := by omega
  rw [arg] at canonical
  have canonical' : RationalCanonical.StoredEmission.costBound
      (emissionWidth B) (workspaceWidth B 0) ≤ 2^125*(B+2)^3 := by
    rw [workspace]
    calc
      _ ≤ 1000000*(2^35*(B+2))^3 := canonical.trans (Nat.mul_le_mul_left _ cube)
      _ ≤ _ := by ring_nf;omega
  have linear : B+2 ≤ (B+2)^3 := le_self_pow₀ (by omega) (by decide)
  have square : (B+2)^2 ≤ (B+2)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have prepare : prepareCost B 0 ≤ 2^110*(B+2)^3 := by
    unfold prepareCost
    have length : plan.length=31 := by decide
    rw [length]
    norm_num [outputList]
    have positive : 1 ≤ (B+2)^3 := one_le_pow₀ (by omega)
    omega
  unfold emissionCost
  have scaled := Nat.mul_le_mul_left 160 (width.trans (Nat.mul_le_mul_left _ linear))
  omega

#print axioms emissionCost_cubic
end Maxwell.Continuum.StoredHeader
