import Maxwell.Continuum.BoxCutoffBasic
import Maxwell.Continuum.BoxCellGeometry
import Maxwell.Continuum.SchwartzMultiplier
import Maxwell.Continuum.CellSpatialFamily

/-! Actual buffered well support gives the cell-localization and
source-preservation equalities used in the finite-box residual. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open CellGauge Bloch MeasureTheory SchwartzMultiplier

theorem schwartz_one_on_interiorCells (n : Fin 3 → ℕ) {b : ℝ} (hb : 0 ≤ b) {x : Space}
    (hx : cellIndex x ∈ interiorCells n b) : schwartz (side n) x = 1 := by
  classical
  apply schwartz_one
  intro j
  have hi := (Finset.mem_filter.mp hx).2 j
  have hs := (spatialBox_mem _ _).mp (mem_spatialBox_index x) j
  exact ⟨by linarith [hi.1, hs.1], by linarith [hi.2, hs.2]⟩

theorem cutoff_preserves_family (n : Fin 3 → ℕ) {b : ℝ} (hb : 0 ≤ b) (f : FieldL2) :
    familyProjection (interiorCells n b) (field (schwartz (side n)) f) =
      familyProjection (interiorCells n b) f := by
  classical
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [familyProjection_ae (interiorCells n b) (field (schwartz (side n)) f) j,
    familyProjection_ae (interiorCells n b) f j, field_ae (schwartz (side n)) f j] with x hl hr hm
  rw [hl, hr, hm]
  by_cases hx : cellIndex x ∈ interiorCells n b
  · rw [ite_eq_left hx, ite_eq_left hx, schwartz_one_on_interiorCells n hb hx, one_mul]
  · rw [ite_eq_right hx, ite_eq_right hx]

theorem cutoff_preserves_source (n : Fin 3 → ℕ) {b : ℝ} (hb : 0 ≤ b) (f : FieldL2)
    (hf : familyProjection (interiorCells n b) f = f) : field (schwartz (side n)) f = f := by
  classical
  apply PiLp.ext
  intro j
  apply Lp.ext
  have ha := familyProjection_ae (interiorCells n b) f j
  rw [hf] at ha
  filter_upwards [ha, field_ae (schwartz (side n)) f j] with x hp hm
  rw [hm]
  by_cases hx : cellIndex x ∈ interiorCells n b
  · rw [schwartz_one_on_interiorCells n hb hx, one_mul]
  · rw [ite_eq_right hx] at hp
    rw [hp, mul_zero]

theorem familyProjection_of_vanishes (F : Finset Alias) (f : FieldL2)
    (hf : ∀ j, ∀ᵐ x ∂volume, cellIndex x ∉ F → f j x = 0) : familyProjection F f = f := by
  classical
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [familyProjection_ae F f j, hf j] with x hp hx
  rw [hp]
  by_cases hm : cellIndex x ∈ F
  · rw [ite_eq_left hm]
  · rw [ite_eq_right hm, hx hm]

theorem well_support_interior {ι : Type*} (n : Fin 3 → ℕ) {L b : ℝ} (hb : 0 ≤ b)
    (r : ι → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8) (f : FieldL2)
    (hf : ∀ j, ∀ᵐ x ∂volume, (∀ i, L ≤ ‖x-r i‖) → f j x = 0) :
    familyProjection (interiorCells n b) f = f := by
  apply familyProjection_of_vanishes
  intro j
  filter_upwards [hf j] with x hx hnot
  apply hx
  intro i
  by_contra hi
  have hdist : ‖x-r i‖ < L := lt_of_not_ge hi
  apply hnot
  apply index_mem_interiorCells n hb
  intro k
  have hcoord : |x k-r i k| < L := by
    exact (show |x k-r i k| ≤ ‖x-r i‖ by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-r i) k).trans_lt hdist
  have hk := abs_lt.mp hcoord
  exact ⟨by linarith [(hr i k).1, hk.1], by linarith [(hr i k).2, hk.2]⟩

#print axioms well_support_interior

end Maxwell.Continuum.BoxCutoff
