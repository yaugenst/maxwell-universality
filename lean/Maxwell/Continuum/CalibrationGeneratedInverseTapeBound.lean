import Maxwell.Continuum.CalibrationGeneratedInverse
import Maxwell.Continuum.RationalDataflowTapeBound

/-! The cached inverse uses only its small raw rational bank. Retained source
registers can therefore be recovered and reset between basis columns. -/
namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem generatedInverse_tapeBound : generatedInverseCode.tapeBound ≤ 1123 := by
  decide +kernel

#print axioms generatedInverse_tapeBound
end Maxwell.Continuum.Calibration.ArrayDecodeMachine
