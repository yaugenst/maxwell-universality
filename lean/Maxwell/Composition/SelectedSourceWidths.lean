import Maxwell.Composition.SelectedWidths
import Maxwell.Composition.PhysicalSourceAllDraw

/-! The final emitted source has logarithmic rational words on every draw,
including draws with a singular background. -/
noncomputable section
namespace Maxwell.Composition.SelectedSourceWidths
open Maxwell.Realization Maxwell.Composition.SelectedWidths
open Maxwell.Composition.SelectedLogicalBounds Maxwell.Composition.SelectedSpacingBounds
open Maxwell.Composition.SelectedDimensionBounds
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def sourceAmplitudeExponent (R : SelectedPlatform) : ℕ := 128+alphaUpperExponent R+1
def sourcePrecisionExponent (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  PhysicalConstants.sourcePrecisionExponent (backgroundExponent p R) (dimensionExponent p R)
    (alphaExponent p R) (errorExponent p)
def sourceCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  3+sourceAmplitudeExponent R+2*sourcePrecisionExponent p R

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm

theorem source_budget_inverse (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (PhysicalConstants.sourceBudget ((I).alpha R) (I).epsilon ((I).backgroundBudget R)
      (Fintype.card ((I).box R).Edge))⁻¹ ≤ (S.nnz:ℚ)^sourcePrecisionExponent p R :=
  PhysicalConstants.sourceBudget_inverse_literal ((I).alpha R) (I).epsilon ((I).backgroundBudget R)
    ((I).alpha_pos R) (I).epsilon_pos ((I).backgroundBudget_pos R) S.nnz _ _ _ _ _ hm2
    (scales_bound p S hm R hm2 hunit).2 (error_inverse_bound p S hm hm2 hunit)
    (background_bound p S hm R hm2 hunit) (dimension_bound p S hm R hm2 hunit)

theorem unrounded_bound (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (hb : S.source ≠ 0) (J : ℕ) (j : Fin J) (e : ((I).box R).Edge) :
    |PhysicalSource.unrounded R.physical S (I).precision ((I).distance R) ((I).zeta R)
      ((I).zeta_pos R) ((I).zeta_one R) ((I).distance_minimum R) J j ((I).alpha R)
      ((I).coordinates R) (SourceRational.decorated S (I).precision) e| ≤
        (S.nnz:ℚ)^sourceAmplitudeExponent R := by
  have h := PhysicalSource.unrounded_coordinate R.physical S (I).precision ((I).distance R)
    ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) ((I).distance_minimum R) J j
    ((I).alpha R) ((I).alpha_pos R).le ((I).coordinates R)
    (SourceRational.decorated S (I).precision) ((I).coordinates_norm R) e
  have hg : ‖PhysicalSource.realVector (SourceRational.decorated S (I).precision)‖ ≤ S.nnz := by
    change ‖PhysicalSource.exactLogicalSource S (I).precision‖ ≤ _
    rw [PhysicalSource.exactLogicalSource_norm]
    exact PhysicalAccuracy.source_norm_le_nnz S (I).precision hunit hb hm
  have hg' := mul_le_mul_of_nonneg_left hg
    (show (0:ℝ)≤128*((I).alpha R:ℝ) by exact_mod_cast mul_nonneg (by norm_num) ((I).alpha_pos R).le)
  have hpow := mul_bound _ _ _
    (mul_bound _ _ _ (constant_bound S.nnz 128 hm2) (alpha_upper p S hm R hm2) ((I).alpha_pos R).le)
    (y:=(S.nnz:ℚ)) (by simp : (S.nnz:ℚ)≤(S.nnz:ℚ)^1) (by positivity)
  exact_mod_cast (h.trans hg').trans (show 128*((I).alpha R:ℝ)*(S.nnz:ℝ) ≤
    (S.nnz:ℝ)^sourceAmplitudeExponent R by exact_mod_cast hpow)

theorem source_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (hb : S.source ≠ 0) (J : ℕ) (j : Fin J) (e : ((I).box R).Edge) :
    Source.ShortRational ((sourceCoefficient p R*unsignedBitLength (2+S.nnz):ℕ):ℝ)
      (((I).target R J j).source e) := by
  exact selectedRound_short S.nnz (sourceAmplitudeExponent R) 0 (sourcePrecisionExponent p R)
    (PhysicalConstants.sourceBudget ((I).alpha R) (I).epsilon ((I).backgroundBudget R)
      (Fintype.card ((I).box R).Edge))
    (PhysicalConstants.sourceBudget_pos _ _ _ _ ((I).alpha_pos R) (I).epsilon_pos ((I).backgroundBudget_pos R))
    (by simpa only [pow_zero,one_mul] using source_budget_inverse p S hm R hm2 hunit) _
    (unrounded_bound p S hm R hm2 hunit hb J j e)

end Maxwell.Composition.SelectedSourceWidths
