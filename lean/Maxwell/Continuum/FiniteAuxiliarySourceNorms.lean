import Maxwell.Continuum.FiniteAuxiliaryIdealSource
import Maxwell.Continuum.FiniteAuxiliarySourceInverseNorm

/-! Absolute source and field bounds for the actual finite-well response. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants MeasureTheory

attribute [local irreducible] Auxiliary.resolvent realMode muH Qh idealSource auxiliarySource auxiliaryField

variable {ι : Type*} [Fintype ι]

theorem idealSource_norm_le_source {L z α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (r : ι → Space) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (g : BrightSpace ι) : ‖idealSource D (inverse_length_le_1024 hL) r α g‖ ≤ ‖g‖ := by
  have hh := inverse_length_le_1024 hL
  have hs := idealSource_norm_upper D hh r hα (by simpa only [inv_inv] using hdisj) g
  have hL1 := length_ge_one hL
  have hLp := length_pos hL
  have hpow : (2 : ℝ)^128 ≤ L := (power_le_Ls (by have := exponent_large; omega)).trans hL
  have hc : (2 : ℝ)^128*L⁻¹^2 ≤ 1 := by
    rw [inv_pow, mul_inv_le_iff₀ (pow_pos hLp 2), one_mul]
    nlinarith only [hL1, hpow]
  have hc' := mul_le_mul_of_nonneg_left hα1 (show 0 ≤ (2 : ℝ)^128*L⁻¹^2 by positivity)
  have hcoef : (2 : ℝ)^128*α*L⁻¹^2 ≤ 1 := by nlinarith only [hc, hc']
  exact hs.trans ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg g)).trans_eq (one_mul _))

theorem defectResponse_norm {L z σ K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (hα : 0 < α) (hK : 0 ≤ K)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α)
    (g : BrightSpace ι) :
    ‖defectResponse D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)‖ ≤
      (2 : ℝ)^138*K*‖g‖ := by
  have hLp := length_pos hL
  have hc := collection_norm D.h_pos r (by simpa only [inv_inv] using hdisj)
  have hs := idealSource_norm_upper D (inverse_length_le_1024 hL) r hα.le
    (by simpa only [inv_inv] using hdisj) g
  unfold defectResponse
  calc
    _ ≤ (256*K/α)*‖collection L⁻¹ r (resolvent D hσ0 hσ
        (idealSource D (inverse_length_le_1024 hL) r α g))‖ :=
      (A.symm : DefectSpace ι →L[ℂ] DefectSpace ι).le_of_opNorm_le hA _
    _ ≤ (256*K/α)*(1*((4*L^2)*((2 : ℝ)^128*α*L⁻¹^2*‖g‖))) := by
      gcongr
      apply ((collection L⁻¹ r).le_of_opNorm_le hc _).trans
      apply mul_le_mul_of_nonneg_left _ zero_le_one
      apply ((resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le_length D hσ0 hσ) _).trans
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [show (2 : ℝ)^138 = 256*4*2^128 by norm_num]
      field_simp [hα.ne', hLp.ne']

theorem auxiliarySource_norm {L z σ K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α)
    (g : BrightSpace ι) :
    ‖auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)‖ ≤
      (2 : ℝ)^140*K*‖g‖ := by
  have hi := insertion_norm D.h_pos r (by simpa only [inv_inv] using hdisj)
  have hw := defectResponse_norm hL D hσ0 hσ r hα (zero_le_one.trans hK) hdisj A hA g
  have hwi := (insertion L⁻¹ r).le_of_opNorm_le hi
    (defectResponse D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g))
  rw [one_mul] at hwi
  have hf := idealSource_norm_le_source hL D r hα.le hα1 hdisj g
  have ha := norm_add_le (idealSource D (inverse_length_le_1024 hL) r α g)
    (insertion L⁻¹ r (defectResponse D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)))
  have hkg : ‖g‖ ≤ K*‖g‖ := le_mul_of_one_le_left (norm_nonneg _) hK
  have hcn : (1 : ℝ)+2^138 ≤ 2^140 := by norm_num
  have hm := mul_le_mul_of_nonneg_right hcn (show 0 ≤ K*‖g‖ by positivity)
  rw [auxiliarySource]
  nlinarith only [ha, hf, hwi, hw, hkg, hm]

theorem auxiliaryField_norm {L z σ K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α)
    (g : BrightSpace ι) :
    ‖auxiliaryField D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)‖ ≤
      (2 : ℝ)^142*K*L^2*‖g‖ := by
  rw [auxiliaryField]
  apply ((resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le_length D hσ0 hσ) _).trans
  calc
    _ ≤ (4*L^2)*((2 : ℝ)^140*K*‖g‖) := mul_le_mul_of_nonneg_left
      (auxiliarySource_norm hL D hσ0 hσ r hα hα1 hK hdisj A hA g) (by positivity)
    _ = _ := by norm_num; ring

#print axioms auxiliarySource_norm
#print axioms auxiliaryField_norm

end Maxwell.Continuum.FiniteAuxiliary
