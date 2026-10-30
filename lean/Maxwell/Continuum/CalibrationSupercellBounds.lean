import Maxwell.Continuum.CalibrationSupercellInverse

/-! Uniform bounds for the exact and computed complete supercell
inverse. The finite grid contributes no dimension factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand

attribute [local irreducible] fiberResolvent roundedGridFull PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

theorem actualGridInverse_norm {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (r : Fin 3 → ℚ) :
    ‖actualGridInverse z σ r‖ ≤ 4*L^2 := by
  by_cases hr : activeGrid r
  · rw [actualGridInverse,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (cutoff_nonneg _)]
    have hR : ‖fiberResolvent z σ (gridMomentum r)‖ ≤ 4*L^2 := by
      simpa only [inv_pow,inv_inv] using fiberResolvent_norm_le D hσ0 hσ
        (gridMomentum r) (activeGrid_momentum hr)
    exact (mul_le_mul (cutoff_le_one _) hR (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rw [actualGridInverse,cutoff_zero_of_inactive hr,Complex.ofReal_zero,
      zero_smul ℂ (fiberResolvent z σ (gridMomentum r)),norm_zero]
    positivity

namespace Supercell

variable (M : ℕ) [NeZero M]

theorem exactInverse_norm {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) : ‖exactInverse M z σ‖ ≤ 4*L^2 :=
  operator_norm M _ (by positivity) (fun j => actualGridInverse_norm D hσ0 hσ (gridCoordinates M j))

theorem roundedInverse_norm {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (N ell K P : ℕ) (hlog : L ≤ (2 : ℝ)^ell)
    (hK : aliasSteps (N+2) ell ≤ K) (hP : cutoffWorkBits N ell ≤ P) :
    ‖roundedInverse M z σ D hσ0 hσ K P‖ ≤ 5*L^2 := by
  have he := roundedInverse_error M hL z σ D hσ0 hσ N ell K P hlog hK hP
  have hR := exactInverse_norm M D hσ0 hσ
  have hn := norm_le_norm_sub_add (roundedInverse M z σ D hσ0 hσ K P) (exactInverse M z σ)
  rw [norm_sub_rev] at hn
  have hp : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [sq_nonneg (L-1)]

#print axioms roundedInverse_norm

end Supercell
end Maxwell.Continuum.Calibration
