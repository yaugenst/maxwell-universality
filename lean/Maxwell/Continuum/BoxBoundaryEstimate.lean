import Maxwell.Continuum.BoxCutoffSupport
import Maxwell.Continuum.SchwartzCurlBound

/-! The concrete finite-box boundary error follows from the actual
cell resolvent and its weak derivative commutator, with explicit counts
and separation proved for the constructed cell families. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BoxCutoff

open Auxiliary CellGauge FourierSobolev MasterConstants SchwartzMultiplier

theorem cutoff_commutator_norm (n : Fin 3 → ℕ) {f : FieldL2} (Df : H1Data f) :
    ‖curlCurlCommutator (schwartz (side n)) Df‖ ≤ (2 : ℝ)^24*localH1Norm Df (boundaryCells n) := by
  have hb := schwartz_commutator_coefficients (side n)
  have hs := cutoff_derivatives_supported n
  apply (curlCurlCommutator_norm (by positivity : (0 : ℝ) ≤ 2^19)
    (schwartz (side n)) (boundaryCells n) hb.1 hb.2 hs.1 hs.2 Df).trans
  exact mul_le_mul_of_nonneg_right (by norm_num : (24 : ℝ)*2^19 ≤ 2^24) (localH1Norm_nonneg Df _)

theorem cutoff_resolvent_commutator {L z σ b : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (n : Fin 3 → ℕ) {f : FieldL2} (Df : H1Data f)
    (hf : familyProjection (interiorCells n b) f = f)
    (hdf : ∀ j, familyProjection (interiorCells n b) (Df.derivative j) = Df.derivative j) :
    ‖curlCurlCommutator (schwartz (side n)) (resolventH1 D hσ0 hσ Df)‖ ≤
      (2 : ℝ)^26*boundaryCellMajorant L b (∏ j, (n j : ℝ))*Df.norm := by
  have hF : ((boundaryCells n).card : ℝ) ≤ ∏ j, (n j : ℝ) := by exact_mod_cast boundaryCells_card n
  have hG : ((interiorCells n b).card : ℝ) ≤ ∏ j, (n j : ℝ) := by exact_mod_cast interiorCells_card n b
  have hB := separated_resolvent_localH1 hL D hσ0 hσ (boundaryCells n) (interiorCells n b)
    (by positivity) hF hG (fun _ ha _ hc => buffered_cell_distance n b ha hc) Df hf hdf
  apply (cutoff_commutator_norm n (resolventH1 D hσ0 hσ Df)).trans
  apply (mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2^24)).trans_eq
  ring

#print axioms cutoff_resolvent_commutator

end Maxwell.Continuum.BoxCutoff
