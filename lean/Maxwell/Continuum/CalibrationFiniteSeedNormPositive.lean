import Maxwell.Continuum.CalibrationFiniteSeedPhysical
import Maxwell.Continuum.CalibrationGlobalNorm

/-! The actual finite seed has a strictly positive computed normalization
factor. This discharges the reciprocal program's domain condition. -/
noncomputable section
namespace Maxwell.Continuum.Calibration.FiniteAlgorithm
open Supercell MasterConstants
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
attribute [local irreducible] size precision rootBits workPrecision rawSeed
  exactRootSeed FourierData.value

theorem rawSeed_normCenter_pos {L : ℕ} (hL : Ls≤(L:ℝ)) (r N : ℕ) :
    0<FourierData.normCenter (precision L r N) (rawSeed L r N) := by
  have hL0 : 0<L := by exact_mod_cast length_pos hL
  have hs:=scale_lower hL0 r N
  have lower:=exactRootSeed_norm_lower (size L r N) hL (size_even L r N)
    (size_well_geometry L r N) (scale L r N) hs (scale_cast L r N)
    (rootBits L r N) (scale_bound hL0 r N)
  have error : ‖(rawSeed L r N).value-exactRootSeed (size L r N) (scale L r N) hs‖≤
      3*(1/2:ℝ)^(precision L r N) := by
    simpa only [rawSeed] using finiteRootSeed_error (size L r N) (scale L r N) hs
      (precision L r N) (rootBits L r N) (scale_bound hL0 r N)
  have small:=seed_normalize_small L r N
  have triangle:=norm_le_norm_sub_add
    (exactRootSeed (size L r N) (scale L r N) hs) (rawSeed L r N).value
  rw [norm_sub_rev] at triangle
  have nonnegative : (0:ℝ)≤(1/2:ℝ)^(precision L r N) := by positivity
  apply (FourierData.normalizeData_error (precision L r N) (rawSeed L r N) _).1
  linarith

#print axioms rawSeed_normCenter_pos
end Maxwell.Continuum.Calibration.FiniteAlgorithm
