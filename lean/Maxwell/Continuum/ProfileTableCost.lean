import Maxwell.Continuum.ProfileTransformCost

/-! The full table cost includes both signed transforms, floor rounding,
every indexed write, endpoint moments and the correction traversal. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

theorem roundedStoreCost_cap (grid D P U W M il ol B : ℕ)
    (hg : grid≤B) (hD : D≤B) (hP : P≤B) (hW : W≤B) (hM : M≤B)
    (hil : il≤B) (hol : ol≤B) (hr : roundedWidth grid U≤B) (hB : 20≤B) :
    roundedStoreCost grid D P U W M il ol≤2^1407*B^57 := by
  have hb : 1≤B := by omega
  have hc := cosineCost_cap grid D P U W il ol B hg hD hP hW hil hol hr hB
  have hcos := (roundedWidth_components grid U).2.2.1.trans hr
  have h2 : B^2≤B^57 := Nat.pow_le_pow_right hb (by decide)
  have hf : DyadicFloor.costBound P (cosineWidth grid U)≤2^144*B^57 := by
    apply (DyadicFloor.costBound_polynomial P (cosineWidth grid U)).trans
    calc
      _≤2^140*(4*B)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=2^144*B^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  have hw : 2^20*(M+5)^2≤2^22*B^57 := by
    calc
      _≤2^20*(2*B)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=2^22*B^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  unfold roundedStoreCost roundedCost
  omega

theorem roundedTableCost_cap (grid D P U M il B : ℕ)
    (hg : grid≤B) (hD : D≤B) (hP : P≤B) (hM : M≤B)
    (hil : il≤B) (hr : roundedWidth grid U≤B) (hB : 20≤B) :
    roundedTableCost grid D P U M il≤2^1410*B^58 := by
  have hb : 1≤B := by omega
  have body := roundedStoreCost_cap grid D P U (roundedWidth grid U) M il
    (roundedWidth grid U) B hg hD hP hr hM hil hr hr hB
  have cost : D*roundedStoreCost grid D P U (roundedWidth grid U) M il (roundedWidth grid U)
      ≤2^1407*B^58 := by
    calc
      _≤B*(2^1407*B^57) := Nat.mul_le_mul hD body
      _=2^1407*B^58 := by ring
  have count : (D+1)*(13*il+15)≤56*B^58 := by
    calc
      _≤(2*B)*(28*B) := Nat.mul_le_mul (by omega) (by omega)
      _=56*B^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by decide))
  unfold roundedTableCost
  omega

theorem endpointCost_cap (D W len B : ℕ) (hD : D≤B) (hW : W≤B) (hlen : len≤B)
    (he : endpointWorkingWidth D W≤B) (hB : 20≤B) : endpointCost D W len≤2^112*B^3 := by
  have hb : 1≤B := by omega
  have h1 : 1≤B^2 := one_le_pow₀ hb
  have h2 : B^2≤B^3 := Nat.pow_le_pow_right hb (by decide)
  have op := operationCost_cap W B hW hB
  have ope := operationCost_cap (endpointWorkingWidth D W) B he hB
  have read : 2^20*(endpointWorkingWidth D W+5)^2≤2^22*B^2 := by
    calc
      _≤2^20*(2*B)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  have body : 2^20*(endpointWorkingWidth D W+5)^2+5*operationCost (endpointWorkingWidth D W)+1
      ≤2^108*B^2 := by omega
  have loop : D*(2^20*(endpointWorkingWidth D W+5)^2+5*operationCost (endpointWorkingWidth D W)+1)
      ≤2^108*B^3 := by
    calc
      _≤B*(2^108*B^2) := Nat.mul_le_mul hD body
      _=_ := by ring
  have count : (D+1)*(13*len+15)≤56*B^3 := by
    calc
      _≤(2*B)*(28*B) := Nat.mul_le_mul (by omega) (by omega)
      _=56*B^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h2
  have first := op.trans (Nat.mul_le_mul_left (2^104) h2)
  have one : 1≤B^3 := one_le_pow₀ hb
  unfold endpointCost
  omega

theorem correctionMapCost_cap (D W len B : ℕ) (hD : D≤B) (hlen : len≤B)
    (hm : correctionWorkingWidth D W≤B) (hB : 20≤B) : correctionMapCost D W len≤2^112*B^3 := by
  have hb : 1≤B := by omega
  have op := operationCost_cap (correctionWorkingWidth D W) B hm hB
  have hsteps : correctionControl.steps≤8 := by decide
  have hs := Nat.mul_le_mul hsteps op
  have h1 : 1≤B^2 := one_le_pow₀ hb
  have read : 2^21*(correctionWorkingWidth D W+5)^2≤2^23*B^2 := by
    calc
      _≤2^21*(2*B)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _=_ := by ring
  have body : PartArray.mapStepCost correctionControl (correctionWorkingWidth D W)≤2^109*B^2 := by
    unfold PartArray.mapStepCost
    omega
  have loop : D*PartArray.mapStepCost correctionControl (correctionWorkingWidth D W)≤2^109*B^3 := by
    calc
      _≤B*(2^109*B^2) := Nat.mul_le_mul hD body
      _=_ := by ring
  have count : (D+1)*(13*len+15)≤56*B^3 := by
    calc
      _≤(2*B)*(28*B) := Nat.mul_le_mul (by omega) (by omega)
      _=56*B^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by decide))
  unfold correctionMapCost
  omega

theorem finalizeCost_cap (D P W len B : ℕ) (hD : D≤B) (hP : P≤B) (hW : W≤B)
    (hlen : len≤B) (hm : encodedTableWidth D W≤B) (hB : 20≤B) :
    finalizeCost D P W len≤2^120*B^3 := by
  have hb : 1≤B := by omega
  have bits := (natural_bits_le_self D).trans hD
  have he : endpointWorkingWidth D W≤B := by unfold encodedTableWidth correctionWorkingWidth at hm;omega
  have endpoint := endpointCost_cap D W D.bits.length B hD hW bits he hB
  have correction := correctionMapCost_cap D (endpointWorkingWidth D W) D.bits.length B hD bits hm hB
  have op := (operationCost_cap (endpointWorkingWidth D W) B he hB).trans
    (Nat.mul_le_mul_left (2^104) (Nat.pow_le_pow_right hb (by decide : (2:ℕ)≤3)))
  have lin : B≤B^3 := Nat.le_self_pow (by decide) _
  have one : 1≤B^3 := one_le_pow₀ hb
  have powerBits : ((2:ℕ)^P).bits.length=P+1 := by rw [Nat.size_eq_bits_len,Nat.size_pow]
  unfold finalizeCost
  rw [powerBits]
  omega

theorem encodedTableCost_cap (grid D P U W il B : ℕ)
    (hg : grid≤B) (hD : D≤B) (hP : P≤B) (hW : W≤B) (hil : il≤B)
    (hr : roundedWidth grid U≤B) (hm : encodedTableWidth D W≤B) (hB : 20≤B) :
    encodedTableCost grid D P U W il≤2^1412*B^58 := by
  have hb : 1≤B := by omega
  have table := roundedTableCost_cap grid D P U W il B hg hD hP hW hil hr hB
  have correction := (finalizeCost_cap D P W (roundedWidth grid U) B hD hP hW hr hm hB).trans
    (Nat.mul_le_mul_left (2^120) (Nat.pow_le_pow_right hb (by decide : (3:ℕ)≤58)))
  have lin : B≤B^58 := Nat.le_self_pow (by decide) _
  have one : 1≤B^58 := one_le_pow₀ hb
  unfold encodedTableCost
  omega

#print axioms encodedTableCost_cap
end Maxwell.Continuum.Profile.Runtime
