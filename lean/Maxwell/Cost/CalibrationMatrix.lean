import Maxwell.Cost.CalibrationMatrix.PowerSemantics
import Maxwell.Cost.CalibrationMatrix.Pairing
import Maxwell.Cost.CalibrationMatrix.Bounds
import Maxwell.Cost.CalibrationMatrix.Horner.UniformCalibration
import Maxwell.Cost.CalibrationMatrix.SourceInit
import Maxwell.Cost.CalibrationMatrix.NatPower
import Maxwell.Cost.CalibrationMatrix.GeneratedMetadata
import Maxwell.Cost.CalibrationMatrix.Allocation

/-! Actual finite signed-channel matrix-vector multiplication and charged
arithmetic bounds for the common-denominator calibration recurrence, its full
finite inverse-numerator loop, denominator construction, sparse-source
initialization, and exact rational pairing output. -/
