import Maxwell.Continuum.FiniteAuxiliarySourceNorms
import Maxwell.Continuum.FiniteAuxiliarySourceSupport
import Maxwell.Continuum.ParameterSourceRegularityCoarse

/-! The manuscript's H¹ budgets for the actual auxiliary source and
field, with all regularity obtained from the constructed continuum maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FourierSobolev

theorem H1Data.norm_le_sum {f : FieldL2} (Df : H1Data f) :
    Df.norm ≤ ‖f‖+∑ j : Fin 3, ‖Df.derivative j‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun j _ => norm_nonneg (Df.derivative j))
  have hp : 0 ≤ ∑ j : Fin 3, ‖Df.derivative j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith only [hs, mul_nonneg (norm_nonneg f) hp]⟩

end Maxwell.Continuum.FourierSobolev

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

theorem resolventH1_norm_length {L z σ : ℝ} (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) {f : FieldL2} (Df : H1Data f) :
    (resolventH1 D hσ0 hσ Df).norm ≤ (16*L^2)*Df.norm+2000*L^4*‖f‖ := by
  have hr := resolvent_norm_le_length D hσ0 hσ
  have hfield := ((resolvent D hσ0 hσ).le_of_opNorm_le hr f).trans
    (mul_le_mul_of_nonneg_left (CellGauge.h1_field_norm_le Df) (by positivity))
  have hd (j : Fin 3) : ‖(resolventH1 D hσ0 hσ Df).derivative j‖ ≤
      (4*L^2)*Df.norm+448*L^4*‖f‖ := by
    have hb := (derivativeResolvent D hσ0 hσ j).le_of_opNorm_le
      (derivativeResolvent_norm_le D hσ0 hσ j) f
    simp only [inv_pow, inv_inv] at hb
    exact (norm_add_le _ _).trans (add_le_add
      (((resolvent D hσ0 hσ).le_of_opNorm_le hr _).trans
        (mul_le_mul_of_nonneg_left (CellGauge.h1_derivative_norm_le Df j) (by positivity))) hb)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hd j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  have hn := (resolventH1 D hσ0 hσ Df).norm_le_sum
  have hpos : 0 ≤ L^4*‖f‖ := by positivity
  nlinarith only [hn, hsum, hfield, hpos]

variable {ι : Type*} [Fintype ι]

def solvedSourceH1 {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (α : ℝ) (g : BrightSpace ι) :
    H1Data (auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)) :=
  auxiliarySourceH1 D hσ0 hσ r v hv0 (by positivity) hv
    (by simpa only [inv_inv] using hdisj) A hA (idealSourceH1 D (inverse_length_le_1024 hL) r α g)

theorem solvedSourceH1_norm {L z σ K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (hAi : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α)
    (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) (g : BrightSpace ι) :
    (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g).norm ≤
      Cs^4*K^2*α⁻¹*L^4*‖g‖ := by
  have hdi : Pairwise fun i j => Disjoint (Metric.ball (r i) L⁻¹⁻¹) (Metric.ball (r j) L⁻¹⁻¹) := by
    simpa only [inv_inv] using hdisj
  have hb := h1OfAxisBounds_norm _
    (sourceTranslationBound_nonneg D hσ0 hσ r A
      (idealSourceH1 D (inverse_length_le_1024 hL) r α g) (by positivity : 0 ≤ (2 : ℝ)^130*L⁻¹^2))
    (auxiliarySource_axis_bound D hσ0 hσ r v hv0 (by positivity) hv hdi A hA
      (idealSourceH1 D (inverse_length_le_1024 hL) r α g))
  change (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g).norm ≤ _ at hb
  unfold sourceTranslationBound at hb
  simp only [inv_pow, inv_inv] at hb
  apply hb.trans
  exact Parameters.source_H1_budget hL hK hα hα1 (norm_nonneg _)
    (CellGauge.h1_norm_nonneg _) (norm_nonneg _) (by positivity)
    (sourceInverse_norm_length D hσ0 hσ r hdisj A (zero_le_one.trans hK) hα hAi)
    (idealSourceH1_norm D (inverse_length_le_1024 hL) r hα.le hα1 hdi g)
    (auxiliarySource_norm hL D hσ0 hσ r hα hα1 hK hdisj A hAi g) (by rw [inv_pow])

def solvedFieldH1 {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (α : ℝ) (g : BrightSpace ι) :
    H1Data (auxiliaryField D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)) :=
  resolventH1 D hσ0 hσ (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g)

theorem solvedFieldH1_norm {L z σ K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (hAi : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α)
    (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) (g : BrightSpace ι) :
    (solvedFieldH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g).norm ≤
      Cs^5*K^2*α⁻¹*L^6*‖g‖ :=
  (resolventH1_norm_length D hσ0 hσ _).trans
    (Parameters.source_field_H1_budget_coarse hL hK hα hα1 (norm_nonneg _)
      (solvedSourceH1_norm hL D hσ0 hσ r v hv0 hv hdisj A hA hAi hK hα hα1 g)
      (auxiliarySource_norm hL D hσ0 hσ r hα hα1 hK hdisj A hAi g))

#print axioms solvedSourceH1_norm
#print axioms solvedFieldH1_norm

end Maxwell.Continuum.FiniteAuxiliary
