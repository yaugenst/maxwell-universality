import Maxwell.Continuum.ParameterOuterInitializeData
import Maxwell.Cost.Structured.Footprint

/-! Preserve the measured source logarithm across the actual outer search. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem initialized_log (v : ℕ→ℕ) : initializedValues v 2200=v 2200 := by
  simp [initializedValues,finishSetup,poweredValues,powerInputs,powerSetup,seedValues,
    NatAssign.overlay,powerIds,DynamicPower.ids,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,OuterInitial.result,Rational.after,
    Rational.common,OuterInitial.searched,OuterInitial.prepared,OuterInitial.setup,
    GeometricAdapter.clearGeo,Rational.clear,
    show 2200∈OuterInitial.ids by decide +kernel]

theorem loop_protects_log : loopCode.protectsTape 2200=true := by decide +kernel

#print axioms initialized_log
#print axioms loop_protects_log
end Maxwell.Continuum.Parameters.OuterMachine
