import Maxwell.Continuum.WellInteractionBound
import Maxwell.Continuum.PeriodicTubeLattice

/-! The full physical well interaction on the literal integer placement
lattice has the paper's base-three decay rate and L^5 prefactor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary CellGauge Bloch PeriodicBand MasterConstants

def placementCell (L d : ℕ) (ν : Bloch.Alias) : Bloch.Alias :=
  fun j => (L : ℤ) * (d : ℤ) * (placementMatrix.mulVec ν) j

def latticeOneNorm (ν : Bloch.Alias) : ℕ := ∑ j : Fin 3, (ν j).natAbs

theorem latticeOneNorm_cast (ν : Bloch.Alias) :
    (latticeOneNorm ν : ℝ) = ∑ j : Fin 3, |integerVector ν j| := by
  simp only [latticeOneNorm, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs, integerVector_apply]

theorem placementCell_displacement (L d : ℕ) (ν : Bloch.Alias) :
    latticeShift (placementCell L d ν) =
      WithLp.toLp 2 (placedDisplacement (L : ℝ) (d : ℝ) (integerVector ν)) := by
  apply PiLp.ext
  intro j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, placementCell,
    placementMatrix, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
    Int.cast_mul, Int.cast_natCast, placedDisplacement, realPlacementMatrix]
  ring

theorem placementCell_rate {L : ℕ} (hL : 0 < (L : ℝ)) (d : ℕ) (ν : Bloch.Alias) :
    Real.exp (-(99/100 : ℝ)*(L : ℝ)⁻¹*
      dualHessianDistance (latticeShift (placementCell L d ν)).ofLp) ≤
      ((3 : ℝ)^(d * latticeOneNorm ν))⁻¹ := by
  rw [placementCell_displacement]
  have hp := placedDisplacement_phase_log_lower hL (Nat.cast_nonneg d) (integerVector ν)
  rw [optimalTubeShift_phase, ← latticeOneNorm_cast] at hp
  have he : Real.exp (-(Real.log 3 * (d : ℝ) * (latticeOneNorm ν : ℝ))) =
      ((3 : ℝ)^(d * latticeOneNorm ν))⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    have hx : Real.log 3 * (d : ℝ) * (latticeOneNorm ν : ℝ) =
        ((d * latticeOneNorm ν : ℕ) : ℝ) * Real.log 3 := by push_cast; ring
    rw [hx, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  apply (Real.exp_le_exp.mpr (by linarith only [hp])).trans_eq he

theorem full_interaction_bound {L : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4 / 64)
    (d : ℕ) (ν : Bloch.Alias) :
    ‖wellInteraction D hσ0 hσ (placementCell L d ν)‖ ≤
      Cs * (L : ℝ)^5 * (((3 : ℝ)^(d * latticeOneNorm ν))⁻¹ + Real.exp (-cs*(L : ℝ))) := by
  apply (wellInteraction_exponential_master hL D hσ0 hσ (placementCell L d ν)).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (placementCell_rate (length_pos hL) d ν) le_rfl)
    (mul_nonneg Cs_pos.le (pow_nonneg (Nat.cast_nonneg L) 5))

#print axioms placementCell_displacement
#print axioms full_interaction_bound

end Maxwell.Continuum.EffectiveMass
