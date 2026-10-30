import Maxwell.Continuum.CalibrationFiniteCoupling
import Maxwell.Continuum.ContinuumCalibrationResources
import Maxwell.Continuum.ContinuumRealizationSelectedRecovery

/-! The selected continuum construction uses literal finite calibration
algorithms for its auxiliary eigenvalue and all three useful couplings.
There are no external numerical enclosures in this interface. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open Calibration EffectiveMass MasterConstants

attribute [local irreducible] MasterConstants.exponent MasterConstants.Ls
  Parameters.sourceInput muH realMode

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def computedModeInterval : RationalInterval :=
  FiniteAlgorithm.modeInterval (length p S hm) (calibrationRadius p S hm)
    (calibrationPrecision p S hm) (energy p S hm)

def computedCouplingInterval (j : Fin 3) : RationalInterval :=
  FiniteAlgorithm.couplingEnclosure (length p S hm) (spacing p S hm)
    (calibrationPrecision p S hm) (energy p S hm) j

theorem computedModeInterval_contains :
    (computedModeInterval p S hm).Contains (muH (energyCalibration p S hm)
      (inverse_length_le_1024 (length_master p S hm))) :=
  FiniteAlgorithm.modeInterval_contains (length_master p S hm) (calibrationRadius p S hm)
    (calibrationPrecision p S hm) (energy p S hm) (energyCalibration p S hm)

theorem computedModeInterval_width :
    (computedModeInterval p S hm).width=(1/2 : ℚ)^(calibrationPrecision p S hm) :=
  FiniteAlgorithm.modeInterval_width _ _ _ _

theorem computedCouplingInterval_contains (j : Fin 3) :
    (computedCouplingInterval p S hm j).Contains
      (usefulCoupling (length_master p S hm) (energyCalibration p S hm) (spacing p S hm) j) :=
  FiniteAlgorithm.couplingEnclosure_contains (length_master p S hm) (spacing p S hm)
    (calibrationPrecision p S hm) (energy p S hm) (energyCalibration p S hm) j

theorem computedCouplingInterval_width (j : Fin 3) :
    (computedCouplingInterval p S hm j).width=(1/2 : ℚ)^(calibrationPrecision p S hm) :=
  FiniteAlgorithm.couplingEnclosure_width _ _ _ _ _

def computedEnclosures : Enclosures p S hm :=
  enclosuresOfPrecision p S hm (computedModeInterval p S hm) (computedCouplingInterval p S hm)
    (computedModeInterval_contains p S hm) (computedModeInterval_width p S hm).le
    (computedCouplingInterval_contains p S hm) (fun j => (computedCouplingInterval_width p S hm j).le)

theorem computedEnclosures_mode :
    (computedEnclosures p S hm).mode=computedModeInterval p S hm := rfl

theorem computedEnclosures_coupling (j : Fin 3) :
    (computedEnclosures p S hm).coupling j=computedCouplingInterval p S hm j := rfl

theorem computedEnclosures_mode_width :
    (computedEnclosures p S hm).mode.width=(1/2 : ℚ)^(calibrationPrecision p S hm) :=
  computedModeInterval_width p S hm

theorem computedEnclosures_coupling_width (j : Fin 3) :
    ((computedEnclosures p S hm).coupling j).width=(1/2 : ℚ)^(calibrationPrecision p S hm) :=
  computedCouplingInterval_width p S hm j

#print axioms computedEnclosures
#print axioms computedEnclosures_mode_width
#print axioms computedEnclosures_coupling_width

end Maxwell.Continuum.RealizationParameters
