import Maxwell.Continuum.FiniteAuxiliaryEncodedRecovery
import Maxwell.Continuum.CompactTemplateRealReady

/-! Every-field recovery for the literal real emitted source and real
volume tests. All error and precision constants are unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition MeasureTheory
open BoxCutoff Bloch CellGauge SelfAdjointResolvent

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs pecCurlCurl

local instance realEncodedRecoveryDecidableEq (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceIncidence.V S precision) := sourcePECDecidableEq S precision

theorem real_encoded_every_field_recovery
    (S : Source.SparseSystem) (precision : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hbsource : S.source ≠ 0)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S))*
      ((S.nnz : ℝ)/(2*2^precision)) ≤ 1/2)
    {κ K α ε : ℝ} (hκ : 1 ≤ κ) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K)
    (hcondition : (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ κ)
    (hbudget : SourceMediator.inverseBudget S precision κ ≤ K)
    {L d : ℕ} {z σ b : ℝ} (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℚ)
    (hvpos : ∀ i, 0 < (v i : ℝ))
    (hvupper : ∀ i, (v i : ℝ) ≤ (2 : ℝ)^130*(L : ℝ)⁻¹^2) (β : Fin 3 → ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hdiag : ∀ i, |(SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i| ≤
        (1/(2 : ℝ)^196)*(L : ℝ)^2)
    (hv : ∀ i, |(v i : ℝ)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i)| ≤
          (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (hβlower : ∀ j, 3*α ≤ |β j|)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (shift : Alias) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (hr : ∀ i j, b+(L : ℝ)+8 ≤ shiftedRoutedCenters S precision L d shift i j ∧
      shiftedRoutedCenters S precision L d shift i j ≤ side n j-b-(L : ℝ)-8)
    {G e₀ ef δm : ℝ} (he0 : 0 ≤ e₀) (he1 : e₀ ≤ 1/2)
    (hGe : G*e₀ = ε/(2 : ℝ)^27) (hef0 : 0 ≤ ef) (hef : ef ≤ e₀/4)
    (hremainder :
      globalMajorant (∏ j, (n j : ℝ)) (Fintype.card (SourceDecoration.Vertex S precision))
        S.nnz K α L*(Real.exp (-cs*(L : ℝ)^(1/3 : ℝ))+Real.exp (-cs*b/L)) ≤ e₀/2)
    (hδm : δm*((2 : ℝ)^142*K*(L : ℝ)^2) ≤ e₀/4)
    (a : SourceDecoration.Vertex S precision → FieldL2) (ha : ∀ i, ‖a i‖ ≤ 2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume,
      x ∉ Metric.ball (shiftedRoutedCenters S precision L d shift i) (L : ℝ) → a i k x = 0)
    (haerror : ∀ i, ‖a i-siteInsertion (L : ℝ)⁻¹
      (shiftedRoutedCenters S precision L d shift i) (realMode D (inverse_length_le_1024 hL))‖ ≤
        min (ef/4) (e₀/4))
    (P : ℕ) (ĉ : ℚ)
    (hĉ : |(ĉ : ℝ)-α/muH D (inverse_length_le_1024 hL)| ≤ ef/16)
    (hP : (S.nnz : ℝ)*(1/2 : ℝ)^P ≤ ef/16)
    (εout : ScalarDielectric)
    (hmaterial : ‖εout.multiplier-assembledMaterial (L : ℝ)⁻¹ (z+σ)
      (shiftedRoutedCenters S precision L d shift) (fun i => (v i : ℝ))‖ ≤ δm)
    (R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (side n)) εout))
    (hR : ‖R.map‖ ≤ G)
    (u : OperatorDomain (BoxModes.boxDomain (side n)))
    (fout : testL2Closure (BoxModes.boxDomain (side n)))
    (hfout : (fout : FieldL2) = emittedSource S precision P ĉ (fun i => fieldRealProjection (a i)))
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (side n)) εout u-fout‖ ≤ e₀*‖fout‖)
    (Pm : ℕ) (w : SourceDecoration.Vertex S precision → ℚ)
    (hPm : (1/2 : ℝ)^Pm ≤
      ε/((2 : ℝ)^27*max 1 (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)))
    (hw : ∀ i, |(w i : ℝ)-(inner ℂ (fieldRealProjection (a i))
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u)).re| ≤
        ε/((2 : ℝ)^27*max 1 (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)))
    (target : ℚ) (htarget : 0 < target) (htarget1 : target ≤ 1)
    (hprecision : (S.nnz : ℝ)/(2*2^precision) ≤ (target : ℝ)/(64*κ))
    (hεdef : ε = (PhysicalAccuracy.epsilon S precision target : ℝ)/16) :
    fieldConjugation (fout : FieldL2) = (fout : FieldL2) ∧
    (∀ i, fieldConjugation (fieldRealProjection (a i)) = fieldRealProjection (a i)) ∧
    Source.ResidualTarget S ((target : ℝ)/4)
      (sparseMomentDecode S precision (weightedMomentValues Pm v w)) := by
  have hreal : fieldConjugation (fout : FieldL2) = (fout : FieldL2) := by
    rw [hfout]
    exact projected_emittedSource_real S precision P ĉ a
  refine ⟨hreal, (fun i => fieldRealProjection_real (a i)), ?_⟩
  exact encoded_every_field_recovery S precision hunit hm hbsource hp hsmall
    hκ hα hα1 hK hcondition hbudget hL D hσ0 hσ hd v hvpos hvupper β
    hε0 hε hfirst hsecond hdiag hv hβ hβlower htail hdt shift n hb hr
    he0 he1 hGe hef0 hef hremainder hδm (fun i => fieldRealProjection (a i))
    (fun i => (fieldRealProjection_norm (a i)).trans (ha i))
    (fun i => fieldRealProjection_supported (a i)
      (Metric.ball (shiftedRoutedCenters S precision L d shift i) (L : ℝ)) (hsa i))
    (fun i => (real_template_error D (inverse_length_le_1024 hL)
      (shiftedRoutedCenters S precision L d shift i) (a i)).trans (haerror i))
    P ĉ hĉ hP εout hmaterial R hR u fout hfout hu Pm w hPm hw target htarget htarget1
    hprecision hεdef

#print axioms real_encoded_every_field_recovery

end Maxwell.Continuum.FiniteAuxiliary
