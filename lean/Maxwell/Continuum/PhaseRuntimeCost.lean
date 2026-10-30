import Maxwell.Continuum.PhaseRuntimeProgram
import Maxwell.Continuum.PhaseMachineFinalCost

/-! Polynomial charged time for the single fixed runtime phase program. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem costBound_polynomial (Q N W : ℕ) :
    costBound Q N W≤2^230*(sizeParameter Q N W)^14 := by
  let X := sizeParameter Q N W
  have hX : 1≤X := by dsimp [X,sizeParameter];omega
  have h1 : 1≤X^14 := one_le_pow₀ hX
  have h2 : X^2≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have h4 : X^4≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have h7 : X^7≤X^14 := Nat.pow_le_pow_right hX (by decide)
  have hW : W+2≤X := by dsimp [X,sizeParameter];omega
  have hx2 : X≤X^2 := Nat.le_self_pow (by decide) _
  have hsetup : setupCost W≤2^81*X^14 := by
    unfold setupCost
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hW 2).trans h2)
  have hm : Machin.Runtime.costBound (Calibration.phaseBits Q N)≤2^120*X^14 :=
    (Machin.Runtime.costBound_polynomial _).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left (phaseBits_size Q N W) 7).trans h7))
  have hseed := fullSeedWidth_polynomial Q N W
  have hmw : machinWidth Q N W+2≤2^40*X^2 := by
    change fullSeedWidth Q N W+2≤2^38*X^2 at hseed
    unfold machinWidth fullSeedWidth at *
    omega
  have hrestore : 2^20*(machinWidth Q N W+2)^2≤2^100*X^14 := by
    calc
      _≤2^20*(2^40*X^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmw 2)
      _=2^100*X^4 := by ring
      _≤_ := Nat.mul_le_mul_left _ h4
  have hp : preparationCost Q N W≤2^220*X^14 :=
    (by unfold preparationCost PhaseMachine.fullCost;omega : preparationCost Q N W≤PhaseMachine.fullCost Q N W+1).trans
      (fullCost_polynomial Q N W)
  have ho : PhaseMachine.order Q N+2≤2^12*X^2 := order_polynomial Q N W
  have hw : fullWorkWidth Q N W+3≤2^51*X^2 := fullWorkWidth_polynomial Q N W
  have hlen := Machin.Runtime.nat_bits_le_self (PhaseMachine.order Q N)
  have hnext := Machin.Runtime.nat_bits_le_self (PhaseMachine.order Q N+1)
  have hinner : fullWorkWidth Q N W+(PhaseMachine.order Q N).bits.length+3≤2^52*X^2 := by omega
  have ht : RationalTaylor.Runtime.costBound (PhaseMachine.order Q N) (fullWorkWidth Q N W)
      (PhaseMachine.order Q N).bits.length≤2^214*X^14 := by
    calc
      _≤2^50*(PhaseMachine.order Q N+2)^5*(fullWorkWidth Q N W+(PhaseMachine.order Q N).bits.length+3)^2 :=
        RationalTaylor.Runtime.costBound_polynomial _ _ _
      _≤2^50*(2^12*X^2)^5*(2^52*X^2)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ho 5)) (Nat.pow_le_pow_left hinner 2)
      _=2^214*X^14 := by ring
  have hclean : 6*(PhaseMachine.order Q N).bits.length+6*(PhaseMachine.order Q N+1).bits.length+33≤2^18*X^14 := by
    have hx : 1≤X^2 := one_le_pow₀ hX
    omega
  calc
    _=setupCost W+Machin.Runtime.costBound (Calibration.phaseBits Q N)+
        2^20*(machinWidth Q N W+2)^2+preparationCost Q N W+
        RationalTaylor.Runtime.costBound (PhaseMachine.order Q N) (fullWorkWidth Q N W)
          (PhaseMachine.order Q N).bits.length+
        (6*(PhaseMachine.order Q N).bits.length+6*(PhaseMachine.order Q N+1).bits.length+33)+1 := by
      unfold costBound machinCost tailCost RationalTaylor.Runtime.cleanCost
      ring
    _≤2^81*X^14+2^120*X^14+2^100*X^14+2^220*X^14+2^214*X^14+2^18*X^14+X^14 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add hsetup hm) hrestore) hp) ht) hclean) h1
    _=(2^81+2^120+2^100+2^220+2^214+2^18+1)*X^14 := by ring
    _≤_ := Nat.mul_le_mul_right _ (by norm_num)

theorem finalValues_width_polynomial (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W i : ℕ) (hi : i∈ids) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) :
    (finalValues negative base a b Q N i).bits.length≤2^67*(sizeParameter Q N W)^4 := by
  have hf := fullFinalWidth_polynomial Q N W
  have hw : W≤sizeParameter Q N W := by unfold sizeParameter;omega
  have h4 : sizeParameter Q N W≤(sizeParameter Q N W)^4 := Nat.le_self_pow (by decide) _
  exact (finalValues_width negative base a b Q N W i hi ha hb hQ hN).trans (by omega)

theorem compiled_run (negative : Bool) (base : RationalTaylor.Runtime.Cycle)
    (a b Q N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b Q N) s.val) (hz : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=negative) :
    ∃t : Store,
      (runPriced ((program base).compile.next input tape) (2^230*(sizeParameter Q N W)^14+1) s.val).finished=
        some (t.place (program base).size) ∧
      (runPriced ((program base).compile.next input tape) (2^230*(sizeParameter Q N W)^14+1) s.val).instructions≤
        2^230*(sizeParameter Q N W)^14 ∧
      NatAssign.Bank ids (finalValues negative base a b Q N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := executes negative base a b Q N W ha hb hQ hN hW input tape s hs hz hsg
  have hbnd := hc.trans (costBound_polynomial Q N W)
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (2^230*(sizeParameter Q N W)^14+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hbnd,bt,zt,ft⟩

#print axioms compiled_run
#print axioms finalValues_width_polynomial
end Maxwell.Continuum.PhaseMachine.Runtime
