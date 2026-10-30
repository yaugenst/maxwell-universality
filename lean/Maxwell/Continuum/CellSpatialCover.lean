import Maxwell.Continuum.CellSpatialFamily
import Maxwell.Continuum.EffectiveMassWell
import Maxwell.Continuum.TranslationContinuity

/-! Actual finite cell covers of translated broad wells. The cover
identities are equalities of physical L² operators, proved from their
literal support and the measurable spatial tiling. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Bloch EffectiveMass MeasureTheory
open scoped InnerProduct

def wellCells (L : ℝ) (k : Bloch.Alias) : Finset Bloch.Alias :=
  (ballCells L).image (fun a => a + k)

theorem wellCells_card (L : ℝ) (k : Bloch.Alias) : (wellCells L k).card = (ballCells L).card := by
  classical
  exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem wellCells_card_le {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias) :
    ((wellCells L k).card : ℝ) ≤ (2 : ℝ)^10 * L^3 := by
  rw [wellCells_card]
  exact ballCells_card_le hL

theorem latticeShift_add (a b : Bloch.Alias) : latticeShift (a+b) = latticeShift a + latticeShift b := by
  apply PiLp.ext
  intro j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, Pi.add_apply,
    PiLp.add_apply, Int.cast_add, smul_eq_mul]
  ring

theorem latticeShift_zero : latticeShift 0 = 0 := by
  apply PiLp.ext
  intro j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, Pi.zero_apply,
    PiLp.zero_apply, Int.cast_zero, smul_eq_mul, mul_zero]

theorem cellIndex_sub_shift (x : Space) (k : Bloch.Alias) :
    cellIndex x = cellIndex (x - latticeShift k) + k := by
  apply (spatialBox_iff_index _ _).mp
  rw [spatialBox_mem]
  have hm := (spatialBox_mem _ _).mp (mem_spatialBox_index (x-latticeShift k))
  intro j
  have hj := hm j
  change 2 * (cellIndex (x-latticeShift k) j : ℝ) < x j - 2 * (k j : ℝ) ∧
    x j - 2 * (k j : ℝ) ≤ 2 * (cellIndex (x-latticeShift k) j : ℝ) + 2 at hj
  simp only [Pi.add_apply, Int.cast_add]
  constructor <;> linarith

theorem cellIndex_mem_wellCells {L : ℝ} (k : Bloch.Alias) {x : Space}
    (hx : ‖x - latticeShift k‖ ≤ L) : cellIndex x ∈ wellCells L k := by
  classical
  rw [wellCells, Finset.mem_image]
  exact ⟨cellIndex (x-latticeShift k), cellIndex_mem_ballCells hx, (cellIndex_sub_shift x k).symm⟩

theorem ballCells_shift_norm_le {L : ℝ} (hL : 1 ≤ L) {a : Bloch.Alias} (ha : a ∈ ballCells L) :
    ‖latticeShift a‖ ≤ 24 * L := by
  have hc (j : Fin 3) : |(a j : ℝ)| ≤ (ballCellRadius L : ℝ) := by
    have hj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ha j)
    exact abs_le.mpr ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
  have hs : ‖latticeShift a‖^2 ≤ 3 * (2 * (ballCellRadius L : ℝ))^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hj (j : Fin 3) : ‖latticeShift a j‖^2 ≤ (2 * (ballCellRadius L : ℝ))^2 := by
      change ‖2 * (a j : ℝ)‖^2 ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (hc j) (by norm_num)
    simp only [Fin.sum_univ_three]
    linarith [hj 0, hj 1, hj 2]
  have hn : ‖latticeShift a‖ ≤ 6 * (ballCellRadius L : ℝ) := by
    nlinarith [norm_nonneg (latticeShift a),
      (show 0 ≤ (ballCellRadius L : ℝ) by positivity)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
  have hN : (ballCellRadius L : ℝ) ≤ L + 3 := by
    simp only [ballCellRadius, Nat.cast_add, Nat.cast_ofNat]
    linarith
  linarith

theorem wellCells_center_norm_le {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias)
    {a : Bloch.Alias} (ha : a ∈ wellCells L k) :
    ‖latticeShift a - latticeShift k‖ ≤ 24 * L := by
  classical
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [latticeShift_add, add_sub_cancel_right]
  exact ballCells_shift_norm_le hL hb

theorem familyProjection_selfAdjoint (F : Finset Bloch.Alias) : IsSelfAdjoint (familyProjection F) := by
  change (familyProjection F)† = familyProjection F
  rw [familyProjection, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact cellProjection_selfAdjoint a

theorem familyProjection_translatedQh {L : ℝ} (hL : 0 < L) (k : Bloch.Alias) (f : FieldL2) :
    familyProjection (wellCells L k) (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)) =
      fieldTranslation (-latticeShift k) (Qh L⁻¹ f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hs := (measurePreserving_add_right volume (-latticeShift k)).quasiMeasurePreserving.ae
    (Qh_supported (inv_pos.mpr hL) f j)
  filter_upwards [familyProjection_ae (wellCells L k)
    (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)) j,
    fieldTranslation_ae (-latticeShift k) (Qh L⁻¹ f) j, hs] with x hp ht hs
  rw [hp]
  by_cases hx : cellIndex x ∈ wellCells L k
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx, ht]
    have hn : L ≤ ‖x-latticeShift k‖ := by
      by_contra h
      exact hx (cellIndex_mem_wellCells k (le_of_lt (lt_of_not_ge h)))
    simp only [inv_inv] at hs
    exact (hs (by simpa only [sub_eq_add_neg] using hn)).symm

theorem familyProjection_Qh {L : ℝ} (hL : 0 < L) :
    (familyProjection (ballCells L)).comp (Qh L⁻¹) = Qh L⁻¹ := by
  apply ContinuousLinearMap.ext
  intro f
  have ht := familyProjection_translatedQh hL (0 : Bloch.Alias) f
  have he : wellCells L (0 : Bloch.Alias) = ballCells L := by simp [wellCells]
  rw [he, latticeShift_zero, neg_zero, fieldTranslation_zero] at ht
  exact ht

theorem Qh_familyProjection {L : ℝ} (hL : 0 < L) :
    (Qh L⁻¹).comp (familyProjection (ballCells L)) = Qh L⁻¹ := by
  have ht := congrArg ContinuousLinearMap.adjoint (familyProjection_Qh hL)
  have hF : (familyProjection (ballCells L))† = familyProjection (ballCells L) :=
    familyProjection_selfAdjoint (ballCells L)
  have hQ : (Qh L⁻¹)† = Qh L⁻¹ := Qh_selfAdjoint L⁻¹
  rw [ContinuousLinearMap.adjoint_comp, hF, hQ] at ht
  exact ht

#print axioms cellIndex_mem_wellCells
#print axioms familyProjection_translatedQh
#print axioms Qh_familyProjection

end Maxwell.Continuum.CellGauge
