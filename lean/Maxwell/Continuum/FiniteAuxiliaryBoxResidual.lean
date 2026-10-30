import Maxwell.Continuum.FiniteAuxiliaryBoxSupport
import Maxwell.Continuum.FiniteAuxiliaryRoutedSource
import Maxwell.Continuum.BoxResidualBudget

/-! The reference-field residual for the actual finite source. Its
regularity, localization and coefficient-sum budgets are all proved
from the constructed auxiliary response and the sparse input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants Bloch CellGauge BoxCutoff
open Maxwell.Composition

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs

variable {ι : Type*} [Fintype ι]

theorem ideal_reference_residual_norm {L z σ b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (r : ι → Space) (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (v : ι → ℝ) (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (α : ℝ) (g : BrightSpace ι) :
    ‖referenceResidual D hσ0 hσ (side n) r v
      (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g)
      (idealSource D (inverse_length_le_1024 hL) r α g)‖ ≤
      Cs*(1+(Fintype.card ι : ℝ))*Real.exp (-cs*L^(1/3 : ℝ))*
        (‖auxiliarySource D hσ0 hσ r A (idealSource D (inverse_length_le_1024 hL) r α g)‖+
          ∑ i, ‖idealCoefficients D (inverse_length_le_1024 hL) α g i‖)+
      (2 : ℝ)^26*boundaryCellMajorant L b (∏ j, (n j : ℝ))*
        (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g).norm := by
  let hh := inverse_length_le_1024 hL
  let f := idealSource D hh r α g
  let Df := solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g
  have heq := auxiliarySource_equation D hσ0 hσ r v (fun i => (hv0 i).ne') A hA f
  have heq' : auxiliarySource D hσ0 hσ r A f =
      (∑ i, idealCoefficients D hh α g i • fieldTranslation (-r i) (actualSource D hh))+
        finiteWellOperator L⁻¹ r v (resolvent D hσ0 hσ (auxiliarySource D hσ0 hσ r A f)) := by
    rw [← idealSource_sum]
    exact heq
  have hg := idealSource_interior hL D n hb r hr α g
  have hg' : familyProjection (interiorCells n b)
      (∑ i, idealCoefficients D hh α g i • fieldTranslation (-r i) (actualSource D hh)) =
      ∑ i, idealCoefficients D hh α g i • fieldTranslation (-r i) (actualSource D hh) := by
    rw [← idealSource_sum]
    exact hg
  have hbnd := reference_residual_norm hL D hσ0 hσ n hb r v (fun i => (hv0 i).le) hv hdisj
    Df (idealCoefficients D hh α g) heq'
    (solvedSource_interior hL D hσ0 hσ n hb r hr v (fun i => (hv0 i).ne') A hA α g)
    (solvedSource_derivative_interior hL D hσ0 hσ n hb r hr v (fun i => (hv0 i).ne') A hA α g Df)
    hg'
  rw [← idealSource_sum] at hbnd
  exact hbnd

theorem routed_reference_residual_budget (S : Source.SparseSystem) (precision : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) {L z σ b K α : ℝ}
    (hL : Ls ≤ L) (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64)
    (n : Fin 3 → ℕ) (hb : 0 ≤ b) (r : SourceDecoration.Vertex S precision → Space)
    (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
    (v : SourceDecoration.Vertex S precision → ℝ)
    (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision))
    (hA : (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision)) = auxiliaryMatrix D hσ0 hσ r v)
    (hAi : ‖(A.symm : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision))‖ ≤ 256*K/α)
    (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) :
    ‖referenceResidual D hσ0 hσ (side n) r v
      (solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α (routedForcing S precision))
      (idealSource D (inverse_length_le_1024 hL) r α (routedForcing S precision))‖ ≤
      globalMajorant (∏ j, (n j : ℝ)) (Fintype.card (SourceDecoration.Vertex S precision)) S.nnz K α L*
        (Real.exp (-cs*L^(1/3 : ℝ))+Real.exp (-cs*b/L))*‖routedForcing S precision‖ := by
  let g := routedForcing S precision
  let hh := inverse_length_le_1024 hL
  let Df := solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g
  have hc : (∑ i, ‖idealCoefficients D hh α g i‖) ≤ (1+(S.nnz : ℝ))*‖g‖ := by
    apply (Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => idealCoefficients_norm_le D hh hα.le hα1 g i)).trans
    exact (routedForcing_sum_le_nnz S precision hunit).trans
      (mul_le_mul_of_nonneg_right (by linarith : (S.nnz : ℝ) ≤ 1+S.nnz) (norm_nonneg _))
  apply (ideal_reference_residual_norm hL D hσ0 hσ n hb r hr v hv0 hv hdisj A hA α g).trans
  exact box_residual_budget (by positivity) (by positivity) (by positivity)
    (zero_le_one.trans hK) hα (length_ge_one hL) (norm_nonneg _)
    (h1_field_norm_le Df)
    (solvedSourceH1_norm hL D hσ0 hσ r v hv0 hv hdisj A hA hAi hK hα hα1 g) hc

#print axioms ideal_reference_residual_norm
#print axioms routed_reference_residual_budget

end Maxwell.Continuum.FiniteAuxiliary
