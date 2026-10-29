import Maxwell.Continuum.SeparatedSymbolCutoff
import Maxwell.Continuum.AuxiliaryResolvent

/-! The actual separated cutoff operator in physical space, built by
the proved Bloch unitary from the complete separated resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic Bloch MeasureTheory PeriodicBand

local instance : NormedSpace ℝ FiberMap := NormedSpace.complexToReal

attribute [local irreducible] separatedSymbol

theorem cutoffSeparatedSymbol_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (q : Space) :
    ‖cutoffSeparatedSymbol z σ q‖ ≤ (2 : ℝ)^112 := by
  by_cases hc : cutoff q = 0
  · rw [cutoffSeparatedSymbol, hc, Complex.ofReal_zero,
      zero_smul ℂ (realSeparatedSymbol z σ q), norm_zero]
    positivity
  · have hq : ‖realMomentumMap q‖ ≤ separatedRadius :=
      (realMomentumMap_norm_le q).trans ((cutoff_ne_zero_norm_le hc).trans
        (cutoff_radius_margin.trans (by linarith [separatedRadius_pos])))
    rw [cutoffSeparatedSymbol, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_nonneg q)]
    have hs := separatedSymbol_norm_le D hσ0 hσ hq
    change cutoff q * ‖separatedSymbol z σ (realMomentumMap q)‖ ≤ _
    exact (mul_le_mul (cutoff_le_one q) hs (norm_nonneg _) (by positivity)).trans_eq (one_mul _)

def separatedData {h z σ : ℝ} (D : Calibration h z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) :
    FiberMultiplier.Data (H := FiberSpace) quasiMeasure ((2 : ℝ)^112) where
  operator q := cutoffSeparatedSymbol z σ q.val
  measurable := ((cutoffSeparatedSymbol_contDiff D hσ0 hσ).continuous.comp
    continuous_subtype_val).aestronglyMeasurable
  nonneg := by positivity
  bound q := cutoffSeparatedSymbol_norm_le D hσ0 hσ q.val

def physicalSeparated {h z σ : ℝ} (D : Calibration h z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) :
    FieldL2 →L[ℂ] FieldL2 := physicalize (separatedData D hσ0 hσ).multiplier

theorem physicalSeparated_ae {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (f : FieldL2) :
    unitary (physicalSeparated D hσ0 hσ f) =ᵐ[quasiMeasure] fun q =>
      cutoffSeparatedSymbol z σ q.val (unitary f q) := by
  rw [physicalSeparated, unitary_physicalize]
  exact (separatedData D hσ0 hσ).multiplier_ae (unitary f)

theorem physicalSeparated_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) :
    ‖physicalSeparated D hσ0 hσ‖ ≤ (2 : ℝ)^112 :=
  physicalize_norm_le _ (by positivity) (separatedData D hσ0 hσ).multiplier_norm_le

#print axioms physicalSeparated_ae
#print axioms physicalSeparated_norm_le

end Maxwell.Continuum.Auxiliary
