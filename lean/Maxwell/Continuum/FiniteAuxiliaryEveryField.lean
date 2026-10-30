import Maxwell.Continuum.FiniteAuxiliaryPECRecovery
import Maxwell.Continuum.FiniteAuxiliaryRoutedReadout
import Maxwell.Continuum.FiniteAuxiliaryTemplateReadout

/-! Every actual PEC graph-domain field recovers the constructed bright
moments. Source regularity, support, and the ideal PEC residual are all
discharged; the remaining error inputs are finite output approximations
and the residual supplied by the Maxwell solver. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass FourierSobolev MasterConstants Bloch CellGauge BoxCutoff
open Maxwell.Composition SelfAdjointResolvent

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs pecCurlCurl

variable (S : Source.SparseSystem) (precision : ℕ)
variable {L z σ b K α : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
  (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64)
  (n : Fin 3 → ℕ) (r : SourceDecoration.Vertex S precision → Space)
  (v : SourceDecoration.Vertex S precision → ℝ)
  (hv0 : ∀ i, 0 < v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*L⁻¹^2)
  (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
  (A : DefectSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
    DefectSpace (SourceDecoration.Vertex S precision))
  (hA : (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
    DefectSpace (SourceDecoration.Vertex S precision)) = auxiliaryMatrix D hσ0 hσ r v)
  (hAi : ‖(A.symm : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
    DefectSpace (SourceDecoration.Vertex S precision))‖ ≤ 256*K/α)
  (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)

local notation "g₀" => routedForcing S precision
local notation "f₀" => idealSource D (inverse_length_le_1024 hL) r α g₀
local notation "Df₀" => solvedSourceH1 hL D hσ0 hσ r v hv0 hv hdisj A hA α g₀
local notation "uRef" => referenceGraph D hσ0 hσ (side n) Df₀
local notation "Ω" => BoxModes.boxDomain (side n)
local notation "Ebound" => (2 : ℝ)^142*K*L^2*‖g₀‖
local notation "Berror" => globalMajorant (∏ j, (n j : ℝ))
  (Fintype.card (SourceDecoration.Vertex S precision)) S.nnz K α L*
  (Real.exp (-cs*L^(1/3 : ℝ))+Real.exp (-cs*b/L))*‖g₀‖

include hAi hK hα hα1

theorem routed_reference_norm :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) uRef‖ ≤ Ebound := by
  apply (reference_norm_le D hσ0 hσ (side n)
    (auxiliarySource D hσ0 hσ r A f₀)).trans
  exact auxiliaryField_norm hL D hσ0 hσ r hα hα1 hK hdisj A hAi g₀

variable (hunit : IsUnit (Source.realMatrix S)) (hb : 0 ≤ b)
  (hr : ∀ i j, b+L+8 ≤ r i j ∧ r i j ≤ side n j-b-L-8)
  (εout : ScalarDielectric)
  (R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (side n)) εout))
  {G η δf δm : ℝ} (hR : ‖R.map‖ ≤ G)
  (u : OperatorDomain (BoxModes.boxDomain (side n)))
  (fout : testL2Closure (BoxModes.boxDomain (side n)))
  (hu : ‖maxwellGraphMap (BoxModes.boxDomain (side n)) εout u-fout‖ ≤ η)
  (hf : ‖(fout : FieldL2)-idealSource D (inverse_length_le_1024 hL) r α
    (routedForcing S precision)‖ ≤ δf)
  (hm : ‖εout.multiplier-assembledMaterial L⁻¹ (z+σ) r v‖ ≤ δm)

include hunit hb hr hR hu hf hm hv0 hv hdisj hA

theorem routed_every_field_distance :
    ‖GraphNorm.inclusion (pecCurlCurl Ω) u-GraphNorm.inclusion (pecCurlCurl Ω) uRef‖ ≤
      G*(η+δf+Berror+δm*Ebound) := by
  have hbnd := routed_reference_residual_budget S precision hunit hL D hσ0 hσ n hb r hr
    v hv0 hv hdisj A hA hAi hK hα hα1
  have hres : ‖(GraphNorm.action (pecCurlCurl Ω) uRef : FieldL2)-
      assembledMaterial L⁻¹ (z+σ) r v (GraphNorm.inclusion (pecCurlCurl Ω) uRef)-f₀‖ ≤ Berror := by
    rw [referenceGraph_residual]
    exact hbnd
  apply (every_field_three_errors Ω εout R hR u uRef fout f₀
    (assembledMaterial L⁻¹ (z+σ) r v) hu hf hres hm).trans
  apply mul_le_mul_of_nonneg_left _ ((norm_nonneg R.map).trans hR)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left
    (routed_reference_norm S precision hL D hσ0 hσ n r v hv0 hv hdisj A hA hAi hK hα hα1)
    ((norm_nonneg _).trans hm)

theorem routed_every_field_moments
    (O : FieldL2 →L[ℂ] BrightSpace (SourceDecoration.Vertex S precision)) {δo : ℝ}
    (hO : ‖O-idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))‖ ≤ δo) :
    ‖O (GraphNorm.inclusion (pecCurlCurl Ω) u)-
      brightResponse D (inverse_length_le_1024 hL) hσ0 hσ r A f₀‖ ≤
      δo*Ebound+(δo+(2 : ℝ)^130*L⁻¹^2)*
        (G*(η+δf+Berror+δm*Ebound)) := by
  have hideal := idealReadout_norm D.h_pos
    (show 0 ≤ (2 : ℝ)^130*L⁻¹^2 by positivity) r v
    (fun i => by rw [abs_of_pos (hv0 i)]; exact hv i)
    (by simpa only [inv_inv] using hdisj) (realMode D (inverse_length_le_1024 hL))
    (realMode_norm D (inverse_length_le_1024 hL))
  have he := finite_observable_error O
    (idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))) hO hideal
    (GraphNorm.inclusion (pecCurlCurl Ω) u) (GraphNorm.inclusion (pecCurlCurl Ω) uRef)
    (routed_every_field_distance S precision hL D hσ0 hσ n r v hv0 hv hdisj A hA hAi hK hα hα1
      hunit hb hr εout R hR u fout hu hf hm)
  have hi : idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))
      (GraphNorm.inclusion (pecCurlCurl Ω) uRef) =
      brightResponse D (inverse_length_le_1024 hL) hσ0 hσ r A f₀ :=
    idealReadout_referenceField hL D hσ0 hσ n hb r hr v (fun i => (hv0 i).ne') A hA f₀
  rw [hi] at he
  apply he.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left
    (routed_reference_norm S precision hL D hσ0 hσ n r v hv0 hv hdisj A hA hAi hK hα hα1)
    ((norm_nonneg _).trans hO)

#print axioms routed_every_field_distance
#print axioms routed_every_field_moments

end Maxwell.Continuum.FiniteAuxiliary
