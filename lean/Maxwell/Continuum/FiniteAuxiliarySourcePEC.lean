import Maxwell.Continuum.FiniteAuxiliarySourceAssembly
import Maxwell.Continuum.FiniteAuxiliaryEveryField
import Maxwell.Continuum.FiniteAuxiliaryFieldRange
import Maxwell.Continuum.FiniteAuxiliaryGeometry
import Maxwell.Continuum.FiniteAuxiliaryResponseTranslation

/-! Sparse input to every-field continuum recovery. The auxiliary inverse
and ideal logical estimate are constructed internally. The inputs left
to the finite encoder are its literal tuning, profile, source and moment
errors; the Maxwell inverse is the actual finite-box detuning event. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition
open BoxCutoff Bloch CellGauge SelfAdjointResolvent

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs pecCurlCurl

variable (S : Source.SparseSystem) (precision : ℕ)
local instance sourcePECDecidableEq : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

def shiftedRoutedCenters (L d : ℕ) (a : Alias) : SourceDecoration.Vertex S precision → Space :=
  fun i => centers L d (SourceDecoration.site S precision) i+latticeShift a

theorem routed_pec_residual
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S))*
      ((S.nnz : ℝ)/(2*2^precision)) ≤ 1/2)
    {κ K α ε : ℝ} (hκ : 1 ≤ κ) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K)
    (hcondition : (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ κ)
    (hbudget : SourceMediator.inverseBudget S precision κ ≤ K)
    {L d : ℕ} {z σ b : ℝ} (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (hvpos : ∀ i, 0 < v i)
    (hvupper : ∀ i, v i ≤ (2 : ℝ)^130*(L : ℝ)⁻¹^2) (β : Fin 3 → ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hdiag : ∀ i, |(SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i| ≤
        (1/(2 : ℝ)^196)*(L : ℝ)^2)
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i)| ≤
          (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (hβlower : ∀ j, 3*α ≤ |β j|)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (a : Alias) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (hr : ∀ i j, b+(L : ℝ)+8 ≤ shiftedRoutedCenters S precision L d a i j ∧
      shiftedRoutedCenters S precision L d a i j ≤ side n j-b-(L : ℝ)-8)
    (εout : ScalarDielectric)
    (R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (side n)) εout))
    {G η δf δm δo : ℝ} (hR : ‖R.map‖ ≤ G)
    (u : OperatorDomain (BoxModes.boxDomain (side n)))
    (fout : testL2Closure (BoxModes.boxDomain (side n)))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (side n)) εout u-fout‖ ≤ η)
    (hf : ‖(fout : FieldL2)-idealSource D (inverse_length_le_1024 hL)
      (shiftedRoutedCenters S precision L d a) α (routedForcing S precision)‖ ≤ δf)
    (hmaterial : ‖εout.multiplier-assembledMaterial (L : ℝ)⁻¹ (z+σ)
      (shiftedRoutedCenters S precision L d a) v‖ ≤ δm)
    (O : FieldL2 →L[ℂ] BrightSpace (SourceDecoration.Vertex S precision))
    (hO : ‖O-idealReadout (L : ℝ)⁻¹ (shiftedRoutedCenters S precision L d a) v
      (realMode D (inverse_length_le_1024 hL))‖ ≤ δo) :
    ‖SourceSubdivision.operator S precision
      (routedReadout S precision (O (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u)))-
        SourceSubdivision.source S precision‖ ≤
      6*((2 : ℝ)^130*(L : ℝ)⁻¹^2*
        (G*(η+δf+
          globalMajorant (∏ j, (n j : ℝ)) (Fintype.card (SourceDecoration.Vertex S precision))
            S.nnz K α L*(Real.exp (-cs*(L : ℝ)^(1/3 : ℝ))+Real.exp (-cs*b/L))*
              ‖routedForcing S precision‖+
          δm*((2 : ℝ)^142*K*(L : ℝ)^2*‖routedForcing S precision‖)))+
        δo*(G*(η+δf+‖routedForcing S precision‖)))+
        ε*‖routedForcing S precision‖/1024 := by
  obtain ⟨A, hA, hAi, hlogical⟩ := exists_routed_response S precision hunit hm hp hsmall
    hκ hα hα1 hK hcondition hbudget hL D hσ0 hσ hd v hvpos β hε0 hε hfirst hsecond
    hdiag hv hβ hβlower htail hdt
  let r := shiftedRoutedCenters S precision L d a
  let g := routedForcing S precision
  let f := idealSource D (inverse_length_le_1024 hL) r α g
  have hA' : (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision)) = auxiliaryMatrix D hσ0 hσ r v := by
    change (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision)) = auxiliaryMatrix D hσ0 hσ
        (fun i => centers L d (SourceDecoration.site S precision) i+latticeShift a) v
    rw [auxiliaryMatrix_common_lattice_shift]
    exact hA
  have hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) (L : ℝ)) (Metric.ball (r j) (L : ℝ)) :=
    shifted_centers_disjoint (length_pos hL) hd (SourceDecoration.site S precision)
      (SourceDecoration.site_injective S precision) (latticeShift a)
  let Df := solvedSourceH1 hL D hσ0 hσ r v hvpos hvupper hdisj A hA' α g
  let uref := referenceGraph D hσ0 hσ (side n) Df
  let w := brightResponse D (inverse_length_le_1024 hL) hσ0 hσ r A f
  have hlogical' : ‖SourceSubdivision.operator S precision (routedReadout S precision w)-
      SourceSubdivision.source S precision‖ ≤ ε*‖g‖/1024 := by
    apply (routed_real_residual S precision w).trans
    have ht := hlogical (ComplexInverse.ofRealVector (SourceSubdivision.source S precision))
    have hw : w = idealReadout (L : ℝ)⁻¹ (centers L d (SourceDecoration.site S precision)) v
        (realMode D (inverse_length_le_1024 hL))
        (auxiliaryField D hσ0 hσ (centers L d (SourceDecoration.site S precision)) A
          (idealSource D (inverse_length_le_1024 hL) (centers L d (SourceDecoration.site S precision)) α g)) := by
      change brightResponse D (inverse_length_le_1024 hL) hσ0 hσ
        (fun i => centers L d (SourceDecoration.site S precision) i+latticeShift a) A
        (idealSource D (inverse_length_le_1024 hL)
          (fun i => centers L d (SourceDecoration.site S precision) i+latticeShift a) α g) = _
      rw [brightResponse_common_lattice_shift]
      symm
      exact idealReadout_auxiliaryField D (inverse_length_le_1024 hL) hσ0 hσ _ v
        (fun i => (hvpos i).ne') A hA _
    rw [hw]
    simpa only [g, routedForcing, complexTerminalInjection_norm] using ht
  have hdist := routed_every_field_distance S precision hL D hσ0 hσ n r v hvpos hvupper hdisj
    A hA' hAi hK hα hα1 hunit hb hr εout R hR u fout hu hf hmaterial
  have hnorm : ‖GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u‖ ≤
      G*(η+δf+‖g‖) := by
    apply (graph_field_norm _ εout R hR u fout hu).trans
    apply mul_le_mul_of_nonneg_left _ ((norm_nonneg R.map).trans hR)
    have hs := finite_source_norm_le hL D r hα.le hα1 hdisj g (fout : FieldL2) hf
    change η+‖(fout : FieldL2)‖ ≤ η+δf+‖g‖
    linarith only [hs]
  have hideal := idealReadout_norm D.h_pos
    (show 0 ≤ (2 : ℝ)^130*(L : ℝ)⁻¹^2 by positivity) r v
    (fun i => by rw [abs_of_pos (hvpos i)]; exact hvupper i)
    (by simpa only [inv_inv] using hdisj) (realMode D (inverse_length_le_1024 hL))
    (realMode_norm D (inverse_length_le_1024 hL))
  have hi : idealReadout (L : ℝ)⁻¹ r v (realMode D (inverse_length_le_1024 hL))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) uref) = w :=
    idealReadout_referenceField hL D hσ0 hσ n hb r hr v (fun i => (hvpos i).ne') A hA' f
  have hmoment := finite_observable_error_actual O
    (idealReadout (L : ℝ)⁻¹ r v (realMode D (inverse_length_le_1024 hL))) hO hideal
    (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u)
    (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) uref) hdist hnorm
  rw [hi] at hmoment
  apply (routed_residual_stability S precision
    (O (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u)) w).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hmoment (by norm_num)) hlogical'

#print axioms routed_pec_residual

end Maxwell.Continuum.FiniteAuxiliary
