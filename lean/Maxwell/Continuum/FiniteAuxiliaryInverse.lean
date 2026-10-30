import Maxwell.Continuum.FiniteAuxiliarySchurBounds
import Maxwell.Composition.Woodbury

/-! The complete continuum auxiliary inverse, constructed from its actual
coercive dark block and the finite bright Schur operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode Sh muH Cs

section Perturbation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_equiv_of_half_error (T : E ≃L[ℂ] E) (A : E →L[ℂ] E)
    {b δ : ℝ} (hT : ‖(T.symm : E →L[ℂ] E)‖ ≤ b)
    (hδ : ‖A-(T : E →L[ℂ] E)‖ ≤ δ) (hsmall : b*δ ≤ 1/2) :
    ∃ S : E ≃L[ℂ] E, (S : E →L[ℂ] E) = A ∧ ‖(S.symm : E →L[ℂ] E)‖ ≤ 2*b := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hT
  have hprod : ‖(T.symm : E →L[ℂ] E)‖*‖A-(T : E →L[ℂ] E)‖ ≤ 1/2 :=
    (mul_le_mul hT hδ (norm_nonneg _) hb).trans hsmall
  have hp : ‖(T.symm : E →L[ℂ] E)‖*‖A-(T : E →L[ℂ] E)‖ < 1 :=
    hprod.trans_lt (by norm_num)
  refine ⟨Composition.perturbationEquiv T (A-(T : E →L[ℂ] E)) hp, ?_, ?_⟩
  · rw [Composition.perturbationEquiv_toContinuousLinearMap]
    abel
  · apply (Composition.perturbation_full_inverse_norm_le T (A-(T : E →L[ℂ] E)) hp).trans
    apply (div_le_iff₀ (sub_pos.mpr hp)).mpr
    nlinarith only [hprod, hT, hb]

end Perturbation

variable {ι : Type*} [Fintype ι]

def fullEquiv {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2)
    (S : BrightSpace ι ≃L[ℂ] BrightSpace ι)
    (hS : (S : BrightSpace ι →L[ℂ] BrightSpace ι) = reducedMatrix D hh M hM) :
    DefectSpace ι ≃L[ℂ] DefectSpace ι :=
  schurFullEquiv M (bright (realMode D hh)) (darkEmbed (realMode D hh))
    (brightCoefficient (realMode D hh)) (darkProject (realMode D hh))
    (darkEquiv D hh M hM) S
    (fun x => (bright_dark_decomposition (realMode D hh) (realMode_norm D hh) x).symm)
    (fun _ => rfl) hS
    (brightCoefficient_bright (realMode D hh) (realMode_norm D hh))
    (brightCoefficient_darkEmbed (realMode D hh))
    (darkProject_bright (realMode D hh)) (darkProject_darkEmbed (realMode D hh))

theorem fullEquiv_toContinuousLinearMap {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2)
    (S : BrightSpace ι ≃L[ℂ] BrightSpace ι)
    (hS : (S : BrightSpace ι →L[ℂ] BrightSpace ι) = reducedMatrix D hh M hM) :
    (fullEquiv D hh M hM S hS : DefectSpace ι →L[ℂ] DefectSpace ι) = M := rfl

theorem fullEquiv_inverse_norm {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (S : BrightSpace ι ≃L[ℂ] BrightSpace ι)
    (hS : (S : BrightSpace ι →L[ℂ] BrightSpace ι) =
      reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM)
    (hmixed : ‖couplingError D hσ0 hσ d position‖*((2 : ℝ)^194*((L : ℝ)⁻¹)^2) ≤ 1) :
    ‖((fullEquiv D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM S hS).symm :
      DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤
      4*‖(S.symm : BrightSpace ι →L[ℂ] BrightSpace ι)‖+(2 : ℝ)^193*((L : ℝ)⁻¹)^2 := by
  let M := auxiliaryMatrix D hσ0 hσ (centers L d position) v
  let u := realMode D hh
  let Dc := darkEquiv D hh M hM
  have hinv := darkEquiv_inverse_norm D hh M hM
  have hinv' : ‖(Dc.symm : DarkSpace ι u →L[ℂ] DarkSpace ι u)‖ ≤
      (2 : ℝ)^194*((L : ℝ)⁻¹)^2 :=
    hinv.trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^193 ≤ 2^194) (sq_nonneg _))
  have hlow := actual_mixed_lower_norm D hh hσ0 hσ d position hinj v
  have hupp := actual_mixed_upper_norm D hh hσ0 hσ d position hinj v
  have hleft : ‖(Dc.symm : DarkSpace ι u →L[ℂ] DarkSpace ι u).comp
      ((darkProject u).comp (M.comp (bright u)))‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have he := mul_le_mul hinv' hlow
      (norm_nonneg ((darkProject u).comp (M.comp (bright u))))
      (by positivity : 0 ≤ (2 : ℝ)^194*((L : ℝ)⁻¹)^2)
    exact he.trans ((mul_comm _ _).trans_le hmixed)
  have hright : ‖((brightCoefficient u).comp (M.comp (darkEmbed u))).comp
      (Dc.symm : DarkSpace ι u →L[ℂ] DarkSpace ι u)‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hupp hinv' (norm_nonneg _) (norm_nonneg _)).trans hmixed)
  have he := schurFullInverse_norm M (bright u) (darkEmbed u) (brightCoefficient u)
    (darkProject u) Dc S
    (bright_norm_le (ι := ι) u (realMode_norm D hh)) (darkEmbed_norm_le (ι := ι) u)
    (brightCoefficient_norm_le (ι := ι) u (realMode_norm D hh)) (darkProject_norm_le (ι := ι) u)
    hleft hright
  exact he.trans (add_le_add le_rfl hinv)

#print axioms exists_equiv_of_half_error
#print axioms fullEquiv_inverse_norm

end Maxwell.Continuum.FiniteAuxiliary
