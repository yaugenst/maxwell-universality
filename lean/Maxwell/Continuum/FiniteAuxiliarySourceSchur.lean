import Maxwell.Continuum.FiniteAuxiliarySchurBounds
import Maxwell.Continuum.FiniteAuxiliarySourceEquation

/-! Exact bright-coordinate recovery from the actual auxiliary source
equation, including all residual components in the infinite complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

variable {ι : Type*} [Fintype ι]

section Abstract
variable {E B C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup C] [NormedSpace ℂ C]

omit [Fintype ι] in
theorem schurResidual_norm_bound (M : E →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hm : ‖(P.comp (M.comp Z)).comp (Dc.symm : C →L[ℂ] C)‖ ≤ 1) :
    ‖schurResidual M Z P R Dc‖ ≤ 2 := by
  have hc := (ContinuousLinearMap.opNorm_comp_le
    ((P.comp (M.comp Z)).comp (Dc.symm : C →L[ℂ] C)) R).trans
    (mul_le_mul hm hR (norm_nonneg _) zero_le_one)
  rw [schurResidual, ← ContinuousLinearMap.comp_assoc]
  exact (norm_sub_le _ _).trans ((add_le_add hP hc).trans_eq (by norm_num))

end Abstract

def reducedResidual {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) : DefectSpace ι →L[ℂ] BrightSpace ι :=
  schurResidual M (darkEmbed (realMode D hh)) (brightCoefficient (realMode D hh))
    (darkProject (realMode D hh)) (darkEquiv D hh M hM)

theorem reducedResidual_bright {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι) (hM : ‖M-baseline D hh‖ ≤ modeGap h/2)
    (g : BrightSpace ι) : reducedResidual D hh M hM (bright (realMode D hh) g) = g := by
  simp only [reducedResidual, schurResidual, sub_apply, ContinuousLinearMap.comp_apply,
    brightCoefficient_bright _ (realMode_norm D hh), darkProject_bright, map_zero, sub_zero]

theorem reducedResidual_norm {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L : ℝ)⁻¹^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (hmixed : ‖couplingError D hσ0 hσ d position‖*((2 : ℝ)^194*(L : ℝ)⁻¹^2) ≤ 1) :
    ‖reducedResidual D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM‖ ≤ 2 := by
  let M := auxiliaryMatrix D hσ0 hσ (centers L d position) v
  let u := realMode D hh
  let Dc := darkEquiv D hh M hM
  have hinv := darkEquiv_inverse_norm D hh M hM
  have hinv' : ‖(Dc.symm : DarkSpace ι u →L[ℂ] DarkSpace ι u)‖ ≤
      (2 : ℝ)^194*(L : ℝ)⁻¹^2 :=
    hinv.trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^193 ≤ 2^194) (sq_nonneg _))
  have hupp := actual_mixed_upper_norm D hh hσ0 hσ d position hinj v
  have hm : ‖((brightCoefficient u).comp (M.comp (darkEmbed u))).comp
      (Dc.symm : DarkSpace ι u →L[ℂ] DarkSpace ι u)‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hupp hinv' (norm_nonneg _) (norm_nonneg _)).trans hmixed)
  exact schurResidual_norm_bound M (darkEmbed u) (brightCoefficient u) (darkProject u) Dc
    (brightCoefficient_norm_le (ι := ι) u (realMode_norm D hh))
    (darkProject_norm_le (ι := ι) u) hm

def brightResponse {h z σ : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) : BrightSpace ι :=
  brightCoefficient (realMode D hh) (defectResponse D hσ0 hσ r A f)

theorem brightResponse_equation {h z σ : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (hM : ‖auxiliaryMatrix D hσ0 hσ r v-baseline D hh‖ ≤ modeGap h/2) (f : FieldL2) :
    reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ r v) hM
      (brightResponse D hh hσ0 hσ r A f) =
      reducedResidual D hh (auxiliaryMatrix D hσ0 hσ r v) hM
        (collection h r (resolvent D hσ0 hσ f)) := by
  have he := schur_action (auxiliaryMatrix D hσ0 hσ r v)
    (bright (realMode D hh)) (darkEmbed (realMode D hh))
    (brightCoefficient (realMode D hh)) (darkProject (realMode D hh))
    (darkEquiv D hh (auxiliaryMatrix D hσ0 hσ r v) hM)
    (fun x => (bright_dark_decomposition (realMode D hh) (realMode_norm D hh) x).symm)
    (fun _ => rfl) (defectResponse D hσ0 hσ r A f)
  change reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ r v) hM
    (brightResponse D hh hσ0 hσ r A f) =
    reducedResidual D hh (auxiliaryMatrix D hσ0 hσ r v) hM
      (auxiliaryMatrix D hσ0 hσ r v (defectResponse D hσ0 hσ r A f)) at he
  have hw : auxiliaryMatrix D hσ0 hσ r v (defectResponse D hσ0 hσ r A f) =
      collection h r (resolvent D hσ0 hσ f) := by
    rw [← hA]
    exact A.apply_symm_apply _
  rw [hw] at he
  exact he

theorem brightResponse_residual_identity {h z σ : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (hM : ‖auxiliaryMatrix D hσ0 hσ r v-baseline D hh‖ ≤ modeGap h/2)
    (f : FieldL2) (α : ℝ) (g : BrightSpace ι) :
    reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ r v) hM
      (brightResponse D hh hσ0 hσ r A f)-(α : ℂ) • g =
    reducedResidual D hh (auxiliaryMatrix D hσ0 hσ r v) hM
      (collection h r (resolvent D hσ0 hσ f)-(α : ℂ) • bright (realMode D hh) g) := by
  rw [brightResponse_equation D hh hσ0 hσ r v A hA hM f, map_sub, map_smul, reducedResidual_bright]

#print axioms reducedResidual_norm
#print axioms brightResponse_residual_identity

end Maxwell.Continuum.FiniteAuxiliary
