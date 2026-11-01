import Maxwell.Cost.CalibrationMatrix.Horner.Cleanup
import Maxwell.Continuum.CalibrationNeumannStep

/-! The continuum inverse exposes the same charged descriptor cleanup as
the shared finite matrix machinery. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix

theorem Snapshot.Ready.bounded_active {n B : ℕ} {a : Snapshot n} {count : List Bool}
    {s : BitRAMState} (h : a.Ready count B s) (size : a.data.Sized B)
    (countWidth : count.length≤B) : WordCleanup.Bounded Horner.activeCleanup B s :=
  Horner.bounded_active h.1 h.2.1 h.2.2 size countWidth

#print axioms Snapshot.Ready.bounded_active
end Maxwell.Continuum.Calibration.NeumannMachine
