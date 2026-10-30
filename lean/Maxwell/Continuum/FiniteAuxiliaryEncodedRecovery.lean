import Maxwell.Continuum.FiniteAuxiliarySourcePEC
import Maxwell.Continuum.FiniteAuxiliaryEncodedReadout
import Maxwell.Continuum.FiniteAuxiliarySourceEncodingSupport

/-! Every-field recovery from the actual emitted n-term dyadic source
and the same compact finite templates used for volume readout. Only
literal calibration/tuning, material and template certificates remain
as inputs; no source, observable or continuum residual bound is assumed. -/

namespace Maxwell.Continuum.FiniteAuxiliary

def weightedMomentValues {ι : Type*} (P : ℕ) (v w : ι → ℚ) : ι → ℚ :=
  fun i => (roundDyadic P (v i*w i)).value

end Maxwell.Continuum.FiniteAuxiliary

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition MeasureTheory
open BoxCutoff Bloch CellGauge SelfAdjointResolvent

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs pecCurlCurl

local instance encodedRecoveryDecidableEq (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceIncidence.V S precision) := sourcePECDecidableEq S precision

theorem encoded_every_field_recovery
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
    (hfout : (fout : FieldL2) = emittedSource S precision P ĉ a)
    (hu : ‖maxwellGraphMap (BoxModes.boxDomain (side n)) εout u-fout‖ ≤ e₀*‖fout‖)
    (Pm : ℕ) (w : SourceDecoration.Vertex S precision → ℚ)
    (hPm : (1/2 : ℝ)^Pm ≤
      ε/((2 : ℝ)^27*max 1 (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)))
    (hw : ∀ i, |(w i : ℝ)-(inner ℂ (a i)
      (GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u)).re| ≤
        ε/((2 : ℝ)^27*max 1 (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)))
    (target : ℚ) (htarget : 0 < target) (htarget1 : target ≤ 1)
    (hprecision : (S.nnz : ℝ)/(2*2^precision) ≤ (target : ℝ)/(64*κ))
    (hεdef : ε = (PhysicalAccuracy.epsilon S precision target : ℝ)/16) :
    Source.ResidualTarget S ((target : ℝ)/4)
      (sparseMomentDecode S precision (weightedMomentValues Pm v w)) := by
  let r := shiftedRoutedCenters S precision L d shift
  let g := ‖routedForcing S precision‖
  let V := (2 : ℝ)^130*(L : ℝ)⁻¹^2
  let O := weightedTemplateReadout (fun i => (v i : ℝ)) a
  let E := GraphNorm.inclusion (pecCurlCurl (BoxModes.boxDomain (side n))) u
  let δy := ε/((2 : ℝ)^27*max 1 (Fintype.card (SourceDecoration.Vertex S precision) : ℝ))
  have hg0 : 0 ≤ g := norm_nonneg _
  have hg1 : 1 ≤ g := (routedForcing_norm_bounds S hbsource precision).1
  have hG : 0 ≤ G := (norm_nonneg R.map).trans hR
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hV : V ≤ 1 := readout_strength_budget hL
  have hvabs : ∀ i, |(v i : ℝ)| ≤ V := by
    intro i
    rw [abs_of_pos (hvpos i)]
    exact hvupper i
  have hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) (L : ℝ))
      (Metric.ball (r j) (L : ℝ)) :=
    shifted_centers_disjoint (length_pos hL) hd (SourceDecoration.site S precision)
      (SourceDecoration.site_injective S precision) (latticeShift shift)
  have hf : ‖(fout : FieldL2)-idealSource D (inverse_length_le_1024 hL) r α
      (routedForcing S precision)‖ ≤ ef*g := by
    rw [hfout]
    exact emittedSource_error S precision hunit hbsource hL D hα.le hα1 r hdisj a ha hsa hef0
      (fun i => (haerror i).trans (min_le_left _ _)) P ĉ hĉ hP
  have hfnorm : ‖fout‖ ≤ 2*g := by
    have hnorm := finite_source_norm_le hL D r hα.le hα1 hdisj (routedForcing S precision)
      (fout : FieldL2) hf
    have hfg := mul_le_mul_of_nonneg_right hef hg0
    have heg := mul_le_mul_of_nonneg_right he1 hg0
    change ‖(fout : FieldL2)‖ ≤ _
    nlinarith only [hnorm, hfg, heg, hg0]
  have hη : e₀*‖fout‖ ≤ 2*e₀*g := by
    exact (mul_le_mul_of_nonneg_left hfnorm he0).trans_eq (by ring)
  have hO : ‖O-idealReadout (L : ℝ)⁻¹ r (fun i => (v i : ℝ))
      (realMode D (inverse_length_le_1024 hL))‖ ≤ e₀/4 :=
    encodedReadout_error hL D (by positivity) r hdisj (fun i => (v i : ℝ)) hvabs a hsa
      (fun i => (haerror i).trans (min_le_right _ _))
  have hlogical := routed_pec_residual S precision hunit hm hp hsmall hκ hα hα1 hK
    hcondition hbudget hL D hσ0 hσ hd (fun i => (v i : ℝ)) hvpos hvupper β hε0 hε
    hfirst hsecond hdiag hv hβ hβlower htail hdt shift n hb hr εout R hR u fout hu hf hmaterial O hO
  have hmessage := message_routed_residual S precision (weightedMomentValues Pm v w) (O E)
    (fun i => weighted_template_round_error Pm v w a E (fun j => (hvabs j).trans hV) hw hPm i)
  have hbudget' := recovery_tolerance_budget hε0 hG hg0 he0 he1 hGe hV0 hV
    (show 0 ≤ e₀*‖fout‖ by positivity) (show 0 ≤ ef*g by positivity) hη
    (show ef*g ≤ e₀*g/4 by nlinarith only [mul_le_mul_of_nonneg_right hef hg0])
    (show globalMajorant (∏ j, (n j : ℝ)) (Fintype.card (SourceDecoration.Vertex S precision))
        S.nnz K α L*(Real.exp (-cs*(L : ℝ)^(1/3 : ℝ))+Real.exp (-cs*b/L))*g ≤ e₀*g/2 by
      nlinarith only [mul_le_mul_of_nonneg_right hremainder hg0])
    (show δm*((2 : ℝ)^142*K*(L : ℝ)^2*g) ≤ e₀*g/4 by
      nlinarith only [mul_le_mul_of_nonneg_right hδm hg0])
    (le_refl (e₀/4)) (message_tolerance_budget (J := Fintype.card (SourceDecoration.Vertex S precision)) hε0 hg1)
  have hfinal : ‖SourceSubdivision.operator S precision
      (routedReadout S precision (rationalMomentVector (weightedMomentValues Pm v w)))-
        SourceSubdivision.source S precision‖ ≤ ε*g/2 := by
    apply (hmessage.trans (add_le_add le_rfl hlogical)).trans
    convert hbudget' using 1
    dsimp only [V, g, O, E, δy]
    ring
  apply messages_source_residual S hunit hm hbsource precision hp κ target hκ htarget htarget1
    hcondition hprecision (weightedMomentValues Pm v w)
  dsimp only [g] at hfinal
  rw [hεdef, routedForcing_norm] at hfinal
  convert hfinal using 1
  ring

#print axioms encoded_every_field_recovery

end Maxwell.Continuum.FiniteAuxiliary
