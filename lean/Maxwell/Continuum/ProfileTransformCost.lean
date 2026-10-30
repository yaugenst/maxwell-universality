import Maxwell.Continuum.ProfileProducerBounds
import Maxwell.Continuum.ProfileAngularCost

/-! Polynomial execution cost of the literal profile transforms, charged
for every scalar call, accumulator update and runtime counter operation. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem natural_bits_le_self (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem operationCost_cap (A B : ℕ) (hA : A≤B) (hB : 20≤B) : operationCost A≤2^104*B^2 := by
  unfold operationCost
  calc
    _≤2^100*(2*B)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _≤_ := by ring_nf;omega

theorem dftStepCost_cap (D P W B : ℕ) (hD : D≤B) (hP : P≤B) (hW : W≤B) (hB : 20≤B) :
    dftStepCost D P W≤2^1400*B^56 := by
  have hb : 1≤B := by omega
  have h1 : 1≤B^56 := one_le_pow₀ hb
  have h14 : B^14≤B^56 := Nat.pow_le_pow_right hb (by decide)
  have h2 : B^2≤B^56 := Nat.pow_le_pow_right hb (by decide)
  have hlin : B≤B^56 := Nat.le_self_pow (by decide) _
  have ha : 96*(W+1)+angularCost P W≤2^1312*B^56 := by
    apply (angularCost_polynomial P W).trans
    calc
      _≤2^1200*(4*B)^56 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 56)
      _=2^1312*B^56 := by ring
  have hp : Phase.Runtime.costBound (D+1) P W≤2^350*B^56 := by
    apply (Phase.Runtime.costBound_polynomial (D+1) P W).trans
    calc
      _≤2^322*(4*B)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 14)
      _=2^350*B^14 := by ring
      _≤_ := Nat.mul_le_mul_left _ h14
  have ho := (operationCost_cap W B hW hB).trans (Nat.mul_le_mul_left (2^104) h2)
  have hl : 64*(W+1)≤128*B^56 := by omega
  unfold dftStepCost
  omega

theorem dftCost_cap (grid D P U W il ol B : ℕ)
    (hg : grid≤B) (hD : D≤B) (hP : P≤B) (hW : W≤B)
    (hil : il≤B) (hol : ol≤B) (hr : roundedWidth grid U≤B) (hB : 20≤B) :
    dftCost grid D P U W il ol≤2^1403*B^57 := by
  have hb : 1≤B := by omega
  have hbits := (natural_bits_le_self grid).trans hg
  obtain ⟨hloop,hnorm,_,_⟩ := roundedWidth_components grid U
  have loop := hloop.trans hr
  have norm := hnorm.trans hr
  have h1 : 1≤B^56 := one_le_pow₀ hb
  have hlin : B≤B^56 := Nat.le_self_pow (by decide) _
  have step := dftStepCost_cap D P (dftLoopWidth grid U) B hD hP loop hB
  have body : dftBodyCost grid D P U grid.bits.length≤2^1401*B^56 := by
    unfold dftBodyCost
    omega
  have initialCost : dftInitializeCost W grid il ol≤2^112*B^2 := by
    have op := operationCost_cap W B hW hB
    have lin : B≤B^2 := Nat.le_self_pow (by decide) _
    have one : 1≤B^2 := one_le_pow₀ hb
    unfold dftInitializeCost
    omega
  have normalize : dftNormalizeCost grid U≤2^108*B^2 := by
    have op := operationCost_cap (dftNormalizationWidth grid U) B norm hB
    have lin : B≤B^2 := Nat.le_self_pow (by decide) _
    have one : 1≤B^2 := one_le_pow₀ hb
    unfold dftNormalizeCost
    omega
  have counter : (grid+1)*(13*grid.bits.length+15)≤56*B^2 := by
    calc
      _≤(2*B)*(28*B) := Nat.mul_le_mul (by omega) (by omega)
      _=56*B^2 := by ring
  have loopcost : grid*dftBodyCost grid D P U grid.bits.length≤2^1401*B^57 := by
    calc
      _≤B*(2^1401*B^56) := Nat.mul_le_mul hg body
      _=2^1401*B^57 := by ring
  have h2 : B^2≤B^57 := Nat.pow_le_pow_right hb (by decide)
  have first := initialCost.trans (Nat.mul_le_mul_left (2^112) h2)
  have last := normalize.trans (Nat.mul_le_mul_left (2^108) h2)
  have count := counter.trans (Nat.mul_le_mul_left 56 h2)
  unfold dftCost
  omega

theorem cosineCost_cap (grid D P U W il ol B : ℕ)
    (hg : grid≤B) (hD : D≤B) (hP : P≤B) (hW : W≤B)
    (hil : il≤B) (hol : ol≤B) (hr : roundedWidth grid U≤B) (hB : 20≤B) :
    cosineCost grid D P U W il ol≤2^1405*B^57 := by
  have hb : 1≤B := by omega
  obtain ⟨_,hn,hc,hd⟩ := roundedWidth_components grid U
  have first := dftCost_cap grid D P U W il ol B hg hD hP hW hil hol hr hB
  have second := dftCost_cap grid D P U (dftNormalizationWidth grid U) il grid.bits.length B
    hg hD hP (hn.trans hr) hil ((natural_bits_le_self grid).trans hg) hr hB
  have op := (operationCost_cap (cosineWidth grid U) B (hc.trans hr) hB).trans
    (Nat.mul_le_mul_left (2^104) (Nat.pow_le_pow_right hb (by decide : (2:ℕ)≤57)))
  have lin : B≤B^57 := Nat.le_self_pow (by decide) _
  have one : 1≤B^57 := one_le_pow₀ hb
  have raw := hd.trans hr
  have cos := hc.trans hr
  unfold cosineCost
  omega

#print axioms dftCost_cap
#print axioms cosineCost_cap
end Maxwell.Continuum.Profile.Runtime
