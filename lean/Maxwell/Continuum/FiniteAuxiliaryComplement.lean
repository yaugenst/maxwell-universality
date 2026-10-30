import Maxwell.Continuum.FiniteAuxiliaryDecomposition

/-! The complementary inverse for the actual interacting continuum wells.
All analytic estimates are discharged by the physical mode gap and the
whole-operator lattice row sums; the remaining hypotheses are scalar
placement and tuning inequalities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode Sh muH

variable {ι : Type*} [Fintype ι]

def darkMatrix {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι) :
    DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh) :=
  (darkProject (realMode D hh)).comp (M.comp (darkEmbed (realMode D hh)))

theorem darkMatrix_difference {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι) :
    ‖darkMatrix D hh M-darkBaseline D hh‖ ≤ ‖M-baseline D hh‖ := by
  rw [← baseline_dark_compression]
  change ‖(darkProject (realMode D hh)).comp (M.comp (darkEmbed (realMode D hh)))-
    (darkProject (realMode D hh)).comp ((baseline D hh).comp (darkEmbed (realMode D hh)))‖ ≤ _
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact contractive_compression_norm _ _ _ (darkProject_norm_le _) (darkEmbed_norm_le _)

theorem darkMatrix_coercive {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) :
    CoerciveInverse.Coercive (darkMatrix D hh M) (modeGap h/2) := by
  have he := coercive_of_norm_sub_le (darkMatrix D hh M) (darkBaseline D hh)
    (darkBaseline_coercive D hh) ((darkMatrix_difference D hh M).trans hM)
  convert he using 1
  ring

def darkEquiv {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) :
    DarkSpace ι (realMode D hh) ≃L[ℂ] DarkSpace ι (realMode D hh) :=
  CoerciveInverse.equiv (darkMatrix D hh M) (half_pos (modeGap_pos D.h_pos))
    (darkMatrix_coercive D hh M hM)

theorem darkEquiv_apply {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) (x : DarkSpace ι (realMode D hh)) :
    darkEquiv D hh M hM x = darkProject (realMode D hh) (M (darkEmbed (realMode D hh) x)) := rfl

theorem darkEquiv_inverse_norm {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (M : DefectSpace ι →L[ℂ] DefectSpace ι)
    (hM : ‖M-baseline D hh‖ ≤ modeGap h/2) :
    ‖((darkEquiv D hh M hM).symm : DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh))‖ ≤
      (2 : ℝ)^193*h^2 := by
  have he := CoerciveInverse.norm_inverse (darkMatrix D hh M)
    (half_pos (modeGap_pos D.h_pos)) (darkMatrix_coercive D hh M hM)
  change ‖((darkEquiv D hh M hM).symm :
    DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh))‖ ≤ _ at he
  apply he.trans_eq
  rw [modeGap, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, inv_inv]
  ring

theorem actual_complement_perturbation {L d : ℕ} {z σ c : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hc : 0 ≤ c) (hv : ∀ i, |(v i)⁻¹-muH D hh| ≤ c)
    (hsmall : c+Cs*(L : ℝ)^5*(64*((3 : ℝ)^d)⁻¹+
        (Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ)))+
        16*σ*((L : ℝ)⁻¹^4)⁻¹ ≤ modeGap (L : ℝ)⁻¹/2) :
    ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤ modeGap (L : ℝ)⁻¹/2 :=
  (auxiliaryMatrix_perturbation_bound hL D hh hσ0 hσ hd position hinj v hc hv).trans hsmall

#print axioms darkEquiv_inverse_norm
#print axioms actual_complement_perturbation

end Maxwell.Continuum.FiniteAuxiliary
