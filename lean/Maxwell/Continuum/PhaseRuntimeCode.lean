import Maxwell.Continuum.PhaseRuntimeCost

/-! A constant compiled-code bound for both runtime phase branches. -/
namespace Maxwell.Continuum.PhaseMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000

theorem core_size_bound (negative : Bool) (base : RationalTaylor.Runtime.Cycle) :
    (core negative base).size≤2^27 := by
  have ht := RationalTaylor.Runtime.program_size_bound (fractionCycle negative base) 655
  have hm := Machin.Runtime.program_size_bound
  have hs : (NatAssign.code setup).size≤2^20 := by decide
  have hscan : (WordLength.code 652 654).size≤2^16 := by decide
  have hr : (NatAssign.code restore).size≤2^16 := by decide
  have hp : preparation.size≤2^20 := by decide
  have hc : (TapeOps.clear 655).code.length≤2^16 := by decide
  have hi : (NatAssign.code RationalTaylor.Runtime.clearIndices).size≤2^16 := by decide
  simp only [core,setupCode,machinCode,tail,RationalTaylor.Runtime.cleanProgram,Code.size]
  omega

theorem program_size_bound (base : RationalTaylor.Runtime.Cycle) : (program base).size≤2^29 := by
  have ht := core_size_bound true base
  have hf := core_size_bound false base
  simp only [program,Code.size]
  omega

#print axioms program_size_bound
end Maxwell.Continuum.PhaseMachine.Runtime
