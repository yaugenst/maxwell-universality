import Maxwell.Continuum.CalibrationCellDecay
import Maxwell.Continuum.CalibrationImageTail
import Maxwell.Continuum.CalibrationImageGeometry

/-! Periodization of the actual complete cell resolvent. The definition
includes every image and the estimate concerns its operator norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge MasterConstants

def imageCellBlock {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (M : ℕ) (a b j : Bloch.Alias) : CellMap :=
  if j = 0 then 0 else resolventCellBlock D hσ0 hσ a (b+M • j)

theorem imageCellBlock_majorant {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) (a b : Bloch.Alias)
    (hd : ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) (j : Bloch.Alias) :
    ‖imageCellBlock D hσ0 hσ M a b j‖ ≤ Cs*L^4*imageTail ((cs/2)*Real.sqrt (M/L)) j := by
  by_cases hj : j = 0
  · simp only [imageCellBlock, imageTail, ite_eq_left hj, norm_zero, mul_zero, le_refl]
  · rw [imageCellBlock, ite_eq_right hj]
    exact (resolventCellBlock_gevrey hL D hσ0 hσ a (b+M • j)).trans
      (mul_le_mul_of_nonneg_left
        (image_distance_decay (length_pos hL) (Nat.cast_nonneg M) j hj (hd j hj))
        (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4)))

theorem imageCellBlock_summable {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) (hM : L ≤ (M : ℝ)) (a b : Bloch.Alias)
    (hd : ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) :
    Summable (fun j => ‖imageCellBlock D hσ0 hσ M a b j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (imageCellBlock_majorant hL D hσ0 hσ M a b hd)
    ((image_tail_sum (length_pos hL) hM).1.mul_left (Cs*L^4))

def periodizedCellBlock {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (M : ℕ) (a b : Bloch.Alias) : CellMap :=
  resolventCellBlock D hσ0 hσ a b + ∑' j, imageCellBlock D hσ0 hσ M a b j

theorem periodizedCellBlock_eq_tsum {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) (hM : L ≤ (M : ℝ)) (a b : Bloch.Alias)
    (hd : ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) :
    periodizedCellBlock D hσ0 hσ M a b =
      ∑' j : Bloch.Alias, resolventCellBlock D hσ0 hσ a (b+M • j) := by
  have hs := (imageCellBlock_summable hL D hσ0 hσ M hM a b hd).of_norm
  have h0 : Summable (fun j : Bloch.Alias =>
      if j = 0 then resolventCellBlock D hσ0 hσ a b else 0) := (hasSum_ite_eq 0 _).summable
  have he (j : Bloch.Alias) : resolventCellBlock D hσ0 hσ a (b+M • j) =
      (if j = 0 then resolventCellBlock D hσ0 hσ a b else 0)+imageCellBlock D hσ0 hσ M a b j := by
    by_cases hj : j = 0 <;> simp [imageCellBlock, hj]
  simp_rw [he]
  rw [h0.tsum_add hs, tsum_ite_eq]
  rfl

theorem periodizedCellBlock_error {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) (hM : L ≤ (M : ℝ)) (a b : Bloch.Alias)
    (hd : ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) :
    ‖periodizedCellBlock D hσ0 hσ M a b-resolventCellBlock D hσ0 hσ a b‖ ≤
      (Cs^2/(2 : ℝ)^32)*L^4*Real.exp (-(cs/4)*Real.sqrt (M/L)) := by
  rw [periodizedCellBlock, add_sub_cancel_left]
  have hs := imageCellBlock_summable hL D hσ0 hσ M hM a b hd
  apply (norm_tsum_le_tsum_norm hs).trans
  calc
    _ ≤ ∑' j : Bloch.Alias, Cs*L^4*imageTail ((cs/2)*Real.sqrt (M/L)) j :=
      hs.tsum_le_tsum (imageCellBlock_majorant hL D hσ0 hσ M a b hd)
        ((image_tail_sum (length_pos hL) hM).1.mul_left (Cs*L^4))
    _ = Cs*L^4*(∑' j : Bloch.Alias, imageTail ((cs/2)*Real.sqrt (M/L)) j) := tsum_mul_left
    _ ≤ Cs*L^4*((Cs/(2 : ℝ)^32)*Real.exp (-(cs/4)*Real.sqrt (M/L))) :=
      mul_le_mul_of_nonneg_left (image_tail_sum (length_pos hL) hM).2
        (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4))
    _ = _ := by ring

#print axioms periodizedCellBlock_eq_tsum
#print axioms periodizedCellBlock_error

end Maxwell.Continuum.Calibration
