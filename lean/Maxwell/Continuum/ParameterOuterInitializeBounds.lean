import Maxwell.Continuum.ParameterOuterInitializeData

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
attribute [local irreducible] OuterInitial.setup

def seedCoefficient : ℕ := 15+2*2^OuterInitial.setup.length
def initialWidthCoefficient : ℕ := seedCoefficient+1026

theorem seed_width_bound (v : ℕ→ℕ) (B : ℕ) :
    seedWidth v B ≤ seedCoefficient*(B+initialExponent (v 2201) (v 2200)+1) := by
  let N := initialExponent (v 2201) (v 2200)
  let X := B+N+1
  let C := 2^OuterInitial.setup.length
  have hX : 1 ≤ X := by unfold X;omega
  have hB : B ≤ X := by unfold X;omega
  have hN : Nat.clog 8 ((v 2200)^6)+1 ≤ X := by
    have h : Nat.clog 8 ((v 2200)^6) ≤ N := le_max_right _ _
    unfold X;omega
  have hp : OuterInitial.preparedWidth B ≤ (2*C)*X := by
    have h := Nat.mul_le_mul_left C (show B+2 ≤ 2*X by unfold X;omega)
    change C*(B+2) ≤ _
    nlinarith only [h]
  have hg : OuterInitial.searchWidth v B ≤ (10+2*C)*X := by
    unfold OuterInitial.searchWidth Geometric.width GeometricAdapter.inputWidth
    nlinarith only [hp,hN,hX]
  have hb : B ≤ (10+2*C)*X := hB.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hm := max_le hb hg
  change seedWidth v B ≤ seedCoefficient*X
  unfold seedWidth seedCoefficient
  change max B (OuterInitial.searchWidth v B)+4 ≤ (15+2*C)*X
  nlinarith only [hm,hX]


#print axioms seed_width_bound

theorem initial_width_bound (v : ℕ→ℕ) (B : ℕ) :
    initialWidth v B ≤ initialWidthCoefficient*(B+initialExponent (v 2201) (v 2200)+1)^2 := by
  let N := initialExponent (v 2201) (v 2200)
  let X := B+N+1
  have hX : 1 ≤ X := by unfold X;omega
  have hs := seed_width_bound v B
  change seedWidth v B ≤ seedCoefficient*X at hs
  have hn : N+1 ≤ X := by unfold X;omega
  have hp : DynamicPower.width N (seedWidth v B) ≤ (seedCoefficient+1)*X^2 := by
    calc
      _ ≤ X*((seedCoefficient+1)*X) := Nat.mul_le_mul hn (by nlinarith only [hs,hX])
      _ = _ := by ring
  have hsq : X ≤ X^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 2)
  have hs' : seedWidth v B ≤ (seedCoefficient+1)*X^2 := hs.trans (by
    have h := Nat.mul_le_mul_left seedCoefficient hsq
    nlinarith only [h,Nat.zero_le (X^2)])
  have hm := max_le hs' hp
  have h1 := Nat.one_le_pow 2 X hX
  change initialWidth v B ≤ initialWidthCoefficient*X^2
  unfold initialWidth initialWidthCoefficient
  change max (seedWidth v B) (DynamicPower.width N (seedWidth v B))+1025 ≤ (seedCoefficient+1026)*X^2
  nlinarith only [hm,h1]


#print axioms initial_width_bound


end Maxwell.Continuum.Parameters.OuterMachine
