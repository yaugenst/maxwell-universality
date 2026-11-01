import Maxwell.Continuum.CalibrationNeumannConverted
import Maxwell.Cost.Structured.TapeBound

/-! Shared-denominator conversion and the inverse recurrence use only the
first three raw rational registers. Retained coefficient cells stay stored. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem converted_tapeBound : convertedCode.tapeBound ≤ 1009 := by
  decide +kernel

#print axioms converted_tapeBound
end Maxwell.Continuum.Calibration.NeumannMachine
