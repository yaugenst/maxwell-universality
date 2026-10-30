import Maxwell.Continuum.ProfileAngularLoaded

/-! Charged polynomial cost of the fixed profile sample evaluator. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2048

private theorem middle_power (X : ℕ) : 2^101*(2^70*X^4)^2=2^241*X^8 := by ring
private theorem glue_power (X : ℕ) : 2^170*(2^70*X^4)^14=2^1150*X^56 := by ring

theorem angularCost_polynomial (P W : ℕ) :
    96*(W+1)+angularCost P W≤2^1200*(P+W+20)^56 := by
  let X := P+W+20
  have hX : 1≤X := by dsimp [X];omega
  have h1 : 1≤X^56 := one_le_pow₀ hX
  have hx : X≤X^4 := Nat.le_self_pow (by decide) _
  have h14 : X^14≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have h8 : X^8≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have h4 : X^4≤X^56 := Nat.pow_le_pow_right hX (by decide)
  have hpow : 1≤X^4 := one_le_pow₀ hX
  have hB : angularMiddleWidth P W+P+14≤2^70*X^4 := by
    have hp : (1+(P+4)+W+12)^4≤X^4 := Nat.pow_le_pow_left (by dsimp [X];omega) 4
    unfold angularMiddleWidth
    have hpw : W+P+24≤2*X := by dsimp [X];omega
    nlinarith only [hp,hpow,hx,hpw]
  have hphase : Phase.Runtime.costBound 1 (P+4) W≤2^322*X^56 := by
    apply (Phase.Runtime.costBound_polynomial 1 (P+4) W).trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp [X];omega) 14).trans h14
  have hmiddle : 2*operationCost (angularMiddleWidth P W)+1≤(2^241+1)*X^56 := by
    have hs : angularMiddleWidth P W+3≤2^70*X^4 := by omega
    have hh := Nat.mul_le_mul_left (2^101) (Nat.pow_le_pow_left hs 2)
    have hp := middle_power X
    rw [hp] at hh
    have hm := Nat.mul_le_mul_left (2^241) h8
    unfold operationCost
    omega
  have hglue : Glue.costBound (P+4) (angularMiddleWidth P W)≤2^1150*X^56 := by
    apply (Glue.costBound_polynomial (P+4) (angularMiddleWidth P W)).trans
    calc
      _≤2^170*(2^70*X^4)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 14)
      _=2^1150*X^56 := glue_power X
  have hload : 96*(W+1)≤96*X^56 := by
    exact Nat.mul_le_mul_left _ ((by dsimp [X];omega : W+1≤X).trans (hx.trans h4))
  unfold angularCost
  change _≤2^1200*X^56
  omega

#print axioms angularCost_polynomial
end Maxwell.Continuum.Profile.Runtime
