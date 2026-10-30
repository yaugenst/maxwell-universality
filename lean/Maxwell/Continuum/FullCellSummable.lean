import Maxwell.Continuum.FullCellLocalization
import Maxwell.Continuum.CellLatticeSummable

/-! Absolute summability of the complete physical resolvent blocks on
the actual infinite period lattice, including every polarization and alias. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch Filter

theorem resolventSpatialBlock_summable {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (a : Bloch.Alias) :
    Summable (fun b : Bloch.Alias => ‖resolventSpatialBlock D hσ0 hσ a b‖) := by
  let C : ℝ := ((2 : ℝ)^68 * (h^2)⁻¹) * ((2 : ℝ)^257/h)^4 * ((4 : ℕ).factorial : ℝ)^2
  apply Summable.of_norm_bounded_eventually ((cellLattice_summable_inverse_four a).mul_left C)
  filter_upwards [eventually_cofinite_ne a] with b hne
  rw [norm_norm]
  have hp := integerVector_sub_norm_pos hne
  have hK := resolventSpatialBlock_polynomial D hh hσ0 hσ a b 4
  rw [latticeShift_sub_norm] at hK
  have hk : ‖integerVector (b-a)‖^4 * ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ C := by
    apply le_trans _ hK
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hp.le (by linarith) 4) (norm_nonneg _)
  calc
    _ ≤ C / ‖integerVector (b-a)‖^4 := (le_div_iff₀ (pow_pos hp 4)).mpr (by simpa [mul_comm] using hk)
    _ = C * ‖integerVector (b-a)‖⁻¹^4 := by rw [div_eq_mul_inv, inv_pow]

theorem resolventSpatialBlock_sum_exists {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (a : Bloch.Alias) :
    Summable (fun b : Bloch.Alias => resolventSpatialBlock D hσ0 hσ a b) :=
  (resolventSpatialBlock_summable D hh hσ0 hσ a).of_norm

#print axioms resolventSpatialBlock_summable
#print axioms resolventSpatialBlock_sum_exists

end Maxwell.Continuum.CellGauge
