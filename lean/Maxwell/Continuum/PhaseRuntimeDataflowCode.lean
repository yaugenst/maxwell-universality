import Maxwell.Continuum.PhaseRuntimeDataflowCost
import Maxwell.Continuum.PhaseRuntimeCode

/-! The shared phase caller also has fixed bounded code; no numeric
precision or Taylor order appears in the instruction-list generator. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem code_size_bound (base : RationalTaylor.Runtime.Cycle) (target source : ℕ) :
    (code base target source).size≤2^32 := by
  have hp : (NatAssign.code (prepareInverse source)).size≤2^20 := by
    change (NatAssign.code (prepareInverse 0)).size≤2^20
    decide
  have hm : RationalMagnitude.program.size≤2^20 := by decide
  have hpre : (NatAssign.code (prepareCall source)).size≤2^20 := by
    change (NatAssign.code (prepareCall 0)).size≤2^20
    decide
  have hcore := PhaseMachine.Runtime.program_size_bound base
  have hf : (NatAssign.code (finishCall target)).size≤2^20 := by
    change (NatAssign.code (finishCall 0)).size≤2^20
    decide
  simp only [code,Code.size,Code.atom,List.length_cons,List.length_nil]
  omega

#print axioms code_size_bound
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
