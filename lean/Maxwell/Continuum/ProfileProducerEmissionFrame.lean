import Maxwell.Continuum.ProfileProducerAllocated
import Maxwell.Continuum.ProgramOutputFootprint
import Maxwell.Continuum.RationalDataflowProgramFootprint

/-! Computing a profile neither emits bits nor modifies the later serializer
cursor tapes; these are finite checks of the literal fixed program. -/
namespace Maxwell.Continuum.Profile.Runtime
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096

def serializerPorts : Finset ℕ := {726,727,728}

theorem producer_preserves_serializer : producerCode.protectsSet serializerPorts=true := by decide
theorem producer_preserves_output : producerCode.protectsOutput=true := by decide

#print axioms producer_preserves_serializer
#print axioms producer_preserves_output
end Maxwell.Continuum.Profile.Runtime
