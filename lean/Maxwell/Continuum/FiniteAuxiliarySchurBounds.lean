import Maxwell.Continuum.FiniteAuxiliarySchur
import Maxwell.Continuum.FiniteAuxiliarySmallness

/-! Quantitative Schur correction for the actual continuum direct sum.
The complementary inverse is the coercive inverse of the complete
interacting dark block. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode Sh muH Cs

section Abstract
variable {E B C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem schurOperator_error_bound (M : E →L[ℂ] E)
    (U : B →L[ℂ] E) (Z : C →L[ℂ] E)
    (P : E →L[ℂ] B) (R : E →L[ℂ] C) (Dc : C ≃L[ℂ] C)
    (Θ : B →L[ℂ] B) {r a b c : ℝ}
    (hr : ‖P.comp (M.comp U)-Θ‖ ≤ r)
    (ha : ‖P.comp (M.comp Z)‖ ≤ a)
    (hb : ‖R.comp (M.comp U)‖ ≤ b)
    (hc : ‖(Dc.symm : C →L[ℂ] C)‖ ≤ c) :
    ‖schurOperator M U Z P R Dc-Θ‖ ≤ r+a*c*b := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  have he : schurOperator M U Z P R Dc-Θ =
      (P.comp (M.comp U)-Θ)-
        (P.comp (M.comp Z)).comp ((Dc.symm : C →L[ℂ] C).comp (R.comp (M.comp U))) := by
    rw [schurOperator]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans (add_le_add hr ?_)
  calc
    ‖(P.comp (M.comp Z)).comp ((Dc.symm : C →L[ℂ] C).comp (R.comp (M.comp U)))‖
        ≤ ‖P.comp (M.comp Z)‖*‖(Dc.symm : C →L[ℂ] C)‖*‖R.comp (M.comp U)‖ := by
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans_eq
              (mul_assoc _ _ _).symm)
    _ ≤ a*c*b := mul_le_mul
      (mul_le_mul ha hc (norm_nonneg _) ha0) hb (norm_nonneg _) (mul_nonneg ha0 hc0)

end Abstract

variable {ι : Type*} [Fintype ι]

def reducedMatrix {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) : BrightSpace ι →L[ℂ] BrightSpace ι :=
  schurOperator M (bright (realMode D hh)) (darkEmbed (realMode D hh))
    (brightCoefficient (realMode D hh)) (darkProject (realMode D hh)) (darkEquiv D hh M hM)

theorem reducedMatrix_error {L : ℕ} {z σ r : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (Θ : BrightSpace ι →L[ℂ] BrightSpace ι)
    (hr : ‖(brightCoefficient (realMode D hh)).comp
      ((auxiliaryMatrix D hσ0 hσ (centers L d position) v).comp (bright (realMode D hh)))-Θ‖ ≤ r) :
    ‖reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM-Θ‖ ≤
      r+‖couplingError D hσ0 hσ d position‖^2*((2 : ℝ)^194*((L : ℝ)⁻¹)^2) := by
  have hinv := darkEquiv_inverse_norm D hh
    (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM
  have hinv' : ‖((darkEquiv D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM).symm :
      DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh))‖ ≤
      (2 : ℝ)^194*((L : ℝ)⁻¹)^2 :=
    hinv.trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^193 ≤ 2^194) (sq_nonneg _))
  have he := schurOperator_error_bound
    (auxiliaryMatrix D hσ0 hσ (centers L d position) v)
    (bright (realMode D hh)) (darkEmbed (realMode D hh))
    (brightCoefficient (realMode D hh)) (darkProject (realMode D hh))
    (darkEquiv D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM) Θ hr
    (actual_mixed_upper_norm D hh hσ0 hσ d position hinj v)
    (actual_mixed_lower_norm D hh hσ0 hσ d position hinj v) hinv'
  dsimp only [reducedMatrix]
  convert he using 1
  ring

#print axioms reducedMatrix_error

end Maxwell.Continuum.FiniteAuxiliary
