import Maxwell.Continuum.PhaseRuntimeMachin
import Maxwell.Continuum.RationalTaylorRuntimeExtension

/-! Complete post-state of the fixed phase evaluator, including every
remaining temporary word that must be charged to later cleanup. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def fractionCycle (negative : Bool) (base : RationalTaylor.Runtime.Cycle) : RationalTaylor.Runtime.Cycle :=
  fun i => (base i).product (if negative then RationalTaylor.Runtime.negativeCycle i
    else RationalTaylor.Runtime.positiveCycle i)
theorem fractionCycle_signs (negative : Bool) (base : RationalTaylor.Runtime.Cycle) :
    RationalTaylor.Runtime.cycleSigns (fractionCycle negative base)=
      fractionSigns negative (RationalTaylor.Runtime.cycleSigns base) := by
  funext n
  change (RationalTaylor.Runtime.cycleSigns base n).product
    (if negative then RationalTaylor.Runtime.cycleSigns RationalTaylor.Runtime.negativeCycle n
      else RationalTaylor.Runtime.cycleSigns RationalTaylor.Runtime.positiveCycle n)=_
  rw [RationalTaylor.Runtime.negativeCycle_signs,RationalTaylor.Runtime.positiveCycle_signs]
  rfl

def preparedValues (a b Q N i : ℕ) : ℕ :=
  if i∈PhaseMachine.allIds then PhaseMachine.fullPrepared a b Q N i else seedValues a b Q N i
def finalValues (negative : Bool) (base : RationalTaylor.Runtime.Cycle) (a b Q N i : ℕ) : ℕ :=
  if i∈PhaseMachine.allIds then
    PhaseMachine.fullFinal negative (RationalTaylor.Runtime.cycleSigns base) a b Q N i
  else if i=655 then 0 else seedValues a b Q N i

theorem seedValues_extra (a b Q N i : ℕ) (hi : i∈extras) :
    seedValues a b Q N i=setupValues a b Q N i := by
  have h630 : i≠630 := by intro h;subst i;exact (show 630∉extras by decide) hi
  have h631 : i≠631 := by intro h;subst i;exact (show 631∉extras by decide) hi
  have hm : i∉Machin.allIds :=
    Finset.disjoint_left.mp (show Disjoint extras Machin.allIds by decide) hi
  simp only [seedValues,restore,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne h630,
    Function.update_of_ne h631,afterMachinValues,ite_eq_right hm]

theorem preparedValues_order (a b Q N : ℕ) : preparedValues a b Q N 655=PhaseMachine.order Q N := by
  simp only [preparedValues,ite_eq_right (by decide : 655∉PhaseMachine.allIds),
    seedValues_extra a b Q N 655 (by decide),setupValues_order]

theorem preparedValues_indices (a b Q N : ℕ) :
    preparedValues a b Q N 607=0 ∧ preparedValues a b Q N 608=0 := by
  constructor
  · simp [preparedValues,show 607∉PhaseMachine.allIds from by decide,
      seedValues_extra a b Q N 607 (by decide),setupValues_eq,scannedValues,initialValues]
  · simp [preparedValues,show 608∉PhaseMachine.allIds from by decide,
      seedValues_extra a b Q N 608 (by decide),setupValues_eq,scannedValues,initialValues]

theorem finalValues_extra (negative : Bool) (base : RationalTaylor.Runtime.Cycle) (a b Q N i : ℕ)
    (hi : i∈extras) : finalValues negative base a b Q N i=
      if i=654 then Q.bits.length else initialValues a b Q N i := by
  have ho : i∉PhaseMachine.allIds :=
    Finset.disjoint_left.mp (show Disjoint extras PhaseMachine.allIds by decide) hi
  have h630 : i≠630 := by intro h;subst i;exact (show 630∉extras by decide) hi
  simp only [finalValues,ite_eq_right ho,seedValues_extra a b Q N i hi,setupValues_eq,ite_eq_right h630]
  by_cases hi655 : i=655
  · subst i
    simp [initialValues]
  · simp [hi655,scannedValues,Function.update_apply]

#print axioms fractionCycle_signs
#print axioms finalValues_extra
end Maxwell.Continuum.PhaseMachine.Runtime
