import Maxwell.Continuum.CalibrationGeneratedInverse
import Maxwell.Cost.Structured.TapeSet

/-! Check the inverse's retained control tapes together, once for its fixed
program. Later callers reuse the same finite footprint certificate. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

def inverseRetainedPorts : Finset ℕ :=
  insert 376 (Finset.Icc 570 584)∪Finset.Icc 116 119∪Finset.Icc 134 139

theorem generatedInverse_retained : generatedInverseCode.protectsSet inverseRetainedPorts=true := by
  decide +kernel

#print axioms generatedInverse_retained
end Maxwell.Continuum.Calibration.ArrayDecodeMachine
