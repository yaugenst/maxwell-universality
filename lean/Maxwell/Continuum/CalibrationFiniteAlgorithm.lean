import Maxwell.Continuum.CalibrationFiniteParameters
import Maxwell.Continuum.CalibrationFiniteSeed
import Maxwell.Continuum.CalibrationFinitePhysical
import Maxwell.Continuum.CalibrationFiniteInner
import Maxwell.Continuum.CalibrationFixedPower

/-! The literal finite mode-calibration program. Every operation is on
stored rational Fourier arrays; all grid sizes, work precision, iteration
counts, and rational normalizations are computed from integer input. -/

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open Supercell

def targetPrecision (N : ℕ) : ℕ := N+4
def iterations (N : ℕ) : ℕ := powerSteps (targetPrecision N)
def workPrecision (N : ℕ) : ℕ := powerWorkPrecision (targetPrecision N)
def size (L r N : ℕ) : ℕ := supercellSize L r (workPrecision N+96) (lengthBits L)

instance size_neZero (L r N : ℕ) : NeZero (size L r N) :=
  ⟨(supercellSize_positive L r (workPrecision N+96) (lengthBits L)).ne'⟩

def rootBits (L r N : ℕ) : ℕ := lengthBits (size L r N)+1
def scale (L r N : ℕ) : ℚ := torusScale L (size L r N)
def precision (L r N : ℕ) : ℕ := workPrecision N+2*lengthBits L+4*rootBits L r N+256
def inverseSteps (L r N : ℕ) : ℕ := aliasSteps (precision L r N+2) (lengthBits L)
def cutoffBits (L r N : ℕ) : ℕ := cutoffWorkBits (precision L r N) (lengthBits L)
def operatorScale (L : ℕ) : ℚ := (2 : ℚ)^90/(L : ℚ)^2

def rawSeed (L r N : ℕ) : FourierData :=
  FourierData.rootApply (scale L r N) (precision L r N) (rootBits L r N)
    (finiteSeed (size L r N) (precision L r N))

def seed (L r N : ℕ) : FourierData :=
  FourierData.normalizeData (precision L r N) (rawSeed L r N)

def rawMode (L r N : ℕ) (z : ℚ) : FourierData :=
  FourierData.iterate (size L r N) (operatorScale L) (scale L r N) z 0
    (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
    (seed L r N) (iterations N)

def mode (L r N : ℕ) (z : ℚ) : FourierData :=
  FourierData.normalizeData (precision L r N) (rawMode L r N z)

def modeImage (L r N : ℕ) (z : ℚ) : FourierData :=
  FourierData.sandwichApply (size L r N) (scale L r N) z 0
    (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
    (mode L r N z)

def eigenvalueCenter (L r N : ℕ) (z : ℚ) : ℚ :=
  (mode L r N z).realInner (modeImage L r N z)

theorem size_even (L r N : ℕ) : Even (size L r N) := supercellSize_even _ _ _ _

theorem size_geometry (L r N : ℕ) :
    16*((L : ℝ)+(r : ℝ)+1) ≤ (size L r N : ℝ) := supercellSize_geometry _ _ _ _

theorem size_accuracy (L r N : ℕ) :
    MasterConstants.Cs^4*(L : ℝ)*
      ((workPrecision N+96 : ℕ)+(lengthBits L : ℝ)+2)^2 ≤ (size L r N : ℝ) :=
  supercellSize_accuracy _ _ _ _

theorem scale_lower {L : ℕ} (hL : 0<L) (r N : ℕ) : 4 ≤ (scale L r N : ℝ) :=
  torusScale_lower hL (by
    have h := size_geometry L r N
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    linarith)

theorem scale_bound {L : ℕ} (hL : 0<L) (r N : ℕ) :
    (scale L r N : ℝ) ≤ (2 : ℝ)^rootBits L r N := torusScale_bound hL

theorem precision_sandwich (L r N : ℕ) :
    cutoffWorkBits (workPrecision N+96) (lengthBits L) ≤ precision L r N := by
  unfold cutoffWorkBits precision
  omega

#print axioms size_accuracy
#print axioms precision_sandwich

end Maxwell.Continuum.Calibration.FiniteAlgorithm
