import Maxwell.Continuum.ParameterOuterResources

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
attribute [local irreducible] OuterInitial.setup powerSetup finishSetup

def initializeCoefficient : ℕ := 3000*8^OuterInitial.setup.length+288*GeometricAdapter.costCoefficient+
  (3000*8^4+8000+3000*8^9+1)+3000*8^powerSetup.length+(2*(3000*8^2)+38)+3000*8^finishSetup.length
def costCoefficient : ℕ := initializeCoefficient+loopCoefficient

theorem initial_covers (v : ℕ→ℕ) (B : ℕ) :
    B ≤ initialWidth v B ∧ seedWidth v B ≤ initialWidth v B ∧
    OuterInitial.searchWidth v B ≤ initialWidth v B ∧ OuterInitial.preparedWidth B ≤ initialWidth v B ∧
    DynamicPower.width (initialExponent (v 2201) (v 2200)) (seedWidth v B) ≤ initialWidth v B ∧
    initialExponent (v 2201) (v 2200)+1 ≤ initialWidth v B ∧ Nat.clog 8 ((v 2200)^6) ≤ initialWidth v B := by
  have hs : seedWidth v B ≤ initialWidth v B := (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hp : DynamicPower.width (initialExponent (v 2201) (v 2200)) (seedWidth v B) ≤ initialWidth v B :=
    (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hb : B ≤ seedWidth v B := (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hg : OuterInitial.searchWidth v B ≤ seedWidth v B := (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hprep : OuterInitial.preparedWidth B ≤ OuterInitial.searchWidth v B := by
    unfold OuterInitial.searchWidth Geometric.width GeometricAdapter.inputWidth
    omega
  have hn : initialExponent (v 2201) (v 2200)+1 ≤ DynamicPower.width (initialExponent (v 2201) (v 2200)) (seedWidth v B) := by
    unfold DynamicPower.width
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hlog : Nat.clog 8 ((v 2200)^6) ≤ initialExponent (v 2201) (v 2200) := le_max_right _ _
  exact ⟨hb.trans hs,hs,hg.trans hs,hprep.trans (hg.trans hs),hp,hn.trans hp,hlog.trans (by omega)⟩

theorem initialize_cost_bound (v : ℕ→ℕ) (B : ℕ) :
    initializeCost v B ≤ initializeCoefficient*(initialWidth v B+1033)^5 := by
  let W := initialWidth v B
  let X := W+1033
  have hX : 1 ≤ X := by unfold X;omega
  obtain ⟨hB,hseed,hsearch,hprep,hpower,hN,hlog⟩ := initial_covers v B
  change B ≤ W at hB
  change seedWidth v B ≤ W at hseed
  change OuterInitial.searchWidth v B ≤ W at hsearch
  change OuterInitial.preparedWidth B ≤ W at hprep
  change DynamicPower.width (initialExponent (v 2201) (v 2200)) (seedWidth v B) ≤ W at hpower
  change initialExponent (v 2201) (v 2200)+1 ≤ W at hN
  change Nat.clog 8 ((v 2200)^6) ≤ W at hlog
  have pow25 : X^2 ≤ X^5 := Nat.pow_le_pow_right hX (by decide)
  have pow35 : X^3 ≤ X^5 := Nat.pow_le_pow_right hX (by decide)
  have square (z c : ℕ) (hz : z ≤ W) (hc : c ≤ 1033) : (z+c)^2 ≤ X^5 :=
    (Nat.pow_le_pow_left (by unfold X;omega) 2).trans pow25
  have head := Nat.mul_le_mul_left (3000*8^OuterInitial.setup.length) (square B 3 hB (by decide))
  have geo := GeometricAdapter.costBound_polynomial (Nat.clog 8 ((v 2200)^6)) 4 (OuterInitial.preparedWidth B)
  have geo' : GeometricAdapter.costBound (Nat.clog 8 ((v 2200)^6)) 4 (OuterInitial.preparedWidth B) ≤
      (288*GeometricAdapter.costCoefficient)*X^5 := by
    calc
      _ ≤ GeometricAdapter.costCoefficient*(4+2)^2*(2*X)^3 := geo.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold X;omega) 3))
      _ = (288*GeometricAdapter.costCoefficient)*X^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ pow35
  have choice : Rational.choiceCostBound (OuterInitial.searchWidth v B) ≤
      (3000*8^4+8000+3000*8^9+1)*X^5 := by
    have hsq := square (OuterInitial.searchWidth v B) 2 hsearch (by decide)
    have ha := Nat.mul_le_mul_left (3000*8^4) hsq
    have hb := Nat.mul_le_mul_left 8000 hsq
    have hc := Nat.mul_le_mul_left (3000*8^9) hsq
    have hone := Nat.one_le_pow 5 X hX
    unfold Rational.choiceCostBound
    nlinarith only [ha,hb,hc,hone]
  have prep := Nat.mul_le_mul_left (3000*8^powerSetup.length) (square (seedWidth v B) 2 hseed (by decide))
  have power : PowerMachine.costBound (initialExponent (v 2201) (v 2200)) (seedWidth v B) ≤
      (2*(3000*8^2)+38)*X^5 := by
    let N := initialExponent (v 2201) (v 2200)
    let A := seedWidth v B
    have hpa : DynamicPower.width N A ≤ W := hpower
    have body := Nat.mul_le_mul_left (3000*8^2) (square A 2 hseed (by decide))
    have bodysq : PowerMachine.bodyCost (DynamicPower.width N A) ≤ (3000*8^2)*X^2 := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (by unfold X;omega) 2
    have loop : N*PowerMachine.bodyCost (DynamicPower.width N A) ≤ (3000*8^2)*X^5 := by
      calc
        _ ≤ X*((3000*8^2)*X^2) := Nat.mul_le_mul (by unfold N X;omega) bodysq
        _ = (3000*8^2)*X^3 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ pow35
    have count : (N+1)*(13*A+15) ≤ 28*X^5 := by
      calc
        _ ≤ X*(28*X) := Nat.mul_le_mul (by unfold N X;omega) (by unfold A X;omega)
        _ = 28*X^2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ pow25
    have clear : 6*A+4 ≤ 10*X^5 := by
      have hm : 6*A+4 ≤ 10*X := by unfold A X;omega
      exact hm.trans (Nat.mul_le_mul_left _ (by simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 5)))
    unfold PowerMachine.costBound PowerMachine.bodyCost
    change (3000*8^2)*(A+2)^2+((N+1)*(13*A+15)+N*((3000*8^2)*(DynamicPower.width N A+2)^2)+(6*A+4)) ≤ _
    unfold PowerMachine.bodyCost at loop
    nlinarith only [body,loop,count,clear]
  have finish := Nat.mul_le_mul_left (3000*8^finishSetup.length) (square W 2 le_rfl (by decide))
  change initializeCost v B ≤ initializeCoefficient*X^5
  unfold initializeCost OuterInitial.costBound initializeCoefficient
  nlinarith only [head,geo',choice,prep,power,finish]

theorem cost_bound (v : ℕ→ℕ) (hD : (dataOf v).Positive) (e B : ℕ) (hℓ : 0<v 2200) :
    costBound v hD e B hℓ ≤ costCoefficient*(resultWidth v hD e B hℓ+1033)^5 := by
  have hi := initialize_cost_bound v B
  have hl := loop_cost_bound (dataOf v) hD e (v 2201) (v 2200) (initialWidth v B) hℓ
  change loopCost (dataOf v) hD e (v 2201) (v 2200) (resultWidth v hD e B hℓ) hℓ ≤
    loopCoefficient*(resultWidth v hD e B hℓ+1033)^5 at hl
  have hw : initialWidth v B ≤ resultWidth v hD e B hℓ := Nat.le_add_right _ _
  have hi' := hi.trans (Nat.mul_le_mul_left initializeCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1033) 5))
  unfold costBound costCoefficient
  nlinarith only [hi',hl]

#print axioms cost_bound
end Maxwell.Continuum.Parameters.OuterMachine
