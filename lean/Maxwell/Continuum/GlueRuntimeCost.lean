import Maxwell.Continuum.GlueRuntimeCore

/-! Polynomial bit-operation bounds for the single fixed glue program. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem order_bound (N W : ℕ) : GlueMachine.order N+2≤16*(N+W+8)^2 := by
  rw [order_eq]
  have h : 8*(N+1)^2+2*N+7+2≤16*(N+8)^2 := by nlinarith
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

theorem resultWidth_bound (N W : ℕ) : resultWidth N W≤2^27*(N+W+8)^4 := by
  let X := N+W+8
  have hX : 1≤X := by dsimp [X];omega
  have hX2 : X≤X^2 := Nat.le_self_pow (by decide) _
  have hk : GlueMachine.order N+2≤16*X^2 := order_bound N W
  have hp : preparedWidth W≤2^20*X := by unfold preparedWidth;dsimp [X];omega
  have hinner : preparedWidth W+GlueMachine.order N+3≤2^21*X^2 := by omega
  have hprod := Nat.mul_le_mul (show GlueMachine.order N+1≤16*X^2 by omega) hinner
  have h1 : 1≤X^4 := one_le_pow₀ hX
  unfold resultWidth RationalTaylor.width
  change _≤2^27*X^4
  nlinarith only [hprod,h1]

theorem expCost_polynomial (N W : ℕ) : expCost N W≤2^121*(N+W+8)^14 := by
  let X := N+W+8
  have hX : 1≤X := by dsimp [X];omega
  have hX2 : X≤X^2 := Nat.le_self_pow (by decide) _
  have h214 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hk : GlueMachine.order N+2≤16*X^2 := order_bound N W
  have hb : (GlueMachine.order N).bits.length≤GlueMachine.order N := nat_bits_le_self _
  have hp : preparedWidth W≤2^20*X := by unfold preparedWidth;dsimp [X];omega
  have hi : preparedWidth W+(GlueMachine.order N).bits.length+3≤2^21*X^2 := by omega
  have hloop := RationalTaylor.Runtime.costBound_polynomial (GlueMachine.order N) (preparedWidth W)
    (GlueMachine.order N).bits.length
  have hl : RationalTaylor.Runtime.costBound (GlueMachine.order N) (preparedWidth W)
      (GlueMachine.order N).bits.length≤2^112*X^14 := by
    calc
      _≤2^50*(GlueMachine.order N+2)^5*(preparedWidth W+(GlueMachine.order N).bits.length+3)^2 := hloop
      _≤2^50*(16*X^2)^5*(2^21*X^2)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 5))
          (Nat.pow_le_pow_left hi 2)
      _=2^112*X^14 := by ring
  have hs : setupWidth W+2≤2^16*X := by unfold setupWidth;dsimp [X];omega
  have hsetup : 2^50*(setupWidth W+2)^2≤2^82*X^14 := by
    calc
      _≤2^50*(2^16*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _=2^82*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h214
  unfold expCost
  change _≤2^121*X^14
  calc
    _≤2^82*X^14+2^112*X^14 := Nat.add_le_add hsetup hl
    _=(2^82+2^112)*X^14 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem costBound_polynomial (N W : ℕ) : costBound N W≤2^124*(N+W+8)^14 := by
  let X := N+W+8
  have hX : 1≤X := by dsimp [X];omega
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have h214 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hw : W+2≤X := by dsimp [X];omega
  have hs : setupWidth W+2≤2^16*X := by unfold setupWidth;dsimp [X];omega
  have hfirst : 2^60*(W+2)^2≤2^60*X^14 :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hw 2).trans h214)
  have hsecond : 2^25*(setupWidth W+2)^2≤2^57*X^14 := by
    calc
      _≤2^25*(2^16*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _=2^57*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h214
  have hthird : 2^50*(setupWidth W+2)^2≤2^82*X^14 := by
    calc
      _≤2^50*(2^16*X)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _=2^82*X^2 := by ring
      _≤_ := Nat.mul_le_mul_left _ h214
  have he : expCost N W≤2^121*X^14 := expCost_polynomial N W
  unfold costBound
  change _≤2^124*X^14
  calc
    _≤2^60*X^14+2^57*X^14+X^14+2^82*X^14+2^121*X^14 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfirst hsecond) h1) hthird) he
    _=(2^60+2^57+1+2^82+2^121)*X^14 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem core_computes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ t : Store, (runPriced (core.compile.next input tape) (2^124*(N+W+8)^14+1) s.val).finished=
        some (t.place core.size) ∧
      (runPriced (core.compile.next input tape) (2^124*(N+W+8)^14+1) s.val).instructions≤
        2^124*(N+W+8)^14 ∧
      Word t.val 602 (result a b N).positive ∧ Word t.val 603 (result a b N).negative ∧
      Word t.val 604 (result a b N).denominator ∧ (result a b N).Valid ∧
      (result a b N).value=(Profile.glueApprox ((a:ℚ)/b) N).center := by
  obtain ⟨cost,t,_,ex,hcost,_,_,_,_,hp,hn,hd,_⟩ := core_executes a b N W ha hb hN hW hb0
    input tape s hs hz
  have hbnd := hcost.trans (costBound_polynomial N W)
  obtain ⟨hrun,hsteps⟩ := ex.compiled_run (2^124*(N+W+8)^14+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hbnd,hp,hn,hd,result_valid a b N hb0,result_value a b N hb0⟩

#print axioms core_computes
#print axioms resultWidth_bound
end Maxwell.Continuum.GlueMachine.Runtime
