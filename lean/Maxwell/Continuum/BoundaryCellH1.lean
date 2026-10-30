import Maxwell.Continuum.CellBounds
import Maxwell.Continuum.CellSpatialSchur

/-! Physical boundary-strip H¹ estimates from the actual cell resolvents.
The derivatives are restricted after differentiation; no H¹ regularity
of a cell-indicator restriction is asserted or needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch FourierSobolev MasterConstants

attribute [local irreducible] Auxiliary.resolvent derivativeResolvent Cs

def boundaryCellMajorant (L b N : ℝ) : ℝ :=
  Cs*L^4*(Real.exp (-cs*b/L)+Real.exp (-cs*L))*N

theorem boundaryCellMajorant_nonneg {L b N : ℝ} (hN : 0 ≤ N) :
    0 ≤ boundaryCellMajorant L b N := by
  unfold boundaryCellMajorant
  have hc := Cs_pos
  positivity

theorem separated_family_resolvent_norm {L z σ b N : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (F G : Finset Bloch.Alias) (hN : 0 ≤ N) (hF : (F.card : ℝ) ≤ N)
    (hG : (G.card : ℝ) ≤ N)
    (hsep : ∀ a ∈ F, ∀ c ∈ G, b ≤ paperCellDistance a c) :
    ‖(familyProjection F).comp ((resolvent D hσ0 hσ).comp (familyProjection G))‖ ≤
      boundaryCellMajorant L b N := by
  unfold boundaryCellMajorant
  have hc0 := Cs_pos
  apply family_block_norm_le_count F G (resolvent D hσ0 hσ) (by positivity) hN hF hG
  intro a ha c hc
  apply (resolventSpatialBlock_paper_exponential hL D hσ0 hσ a c).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg Cs_pos.le (by positivity))
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonpos_left (hsep a ha c hc) (neg_nonpos.mpr cs_pos.le)) (length_pos hL).le

theorem separated_family_derivative_norm {L z σ b N : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (F G : Finset Bloch.Alias) (hN : 0 ≤ N) (hF : (F.card : ℝ) ≤ N)
    (hG : (G.card : ℝ) ≤ N)
    (hsep : ∀ a ∈ F, ∀ c ∈ G, b ≤ paperCellDistance a c) (j : Fin 3) :
    ‖(familyProjection F).comp ((derivativeResolvent D hσ0 hσ j).comp (familyProjection G))‖ ≤
      boundaryCellMajorant L b N := by
  unfold boundaryCellMajorant
  have hc0 := Cs_pos
  apply family_block_norm_le_count F G (derivativeResolvent D hσ0 hσ j) (by positivity) hN hF hG
  intro a ha c hc
  apply (derivativeResolventSpatialBlock_paper_exponential hL D hσ0 hσ j a c).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg Cs_pos.le (by positivity))
  apply add_le_add _ le_rfl
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonpos_left (hsep a ha c hc) (neg_nonpos.mpr cs_pos.le)) (length_pos hL).le

theorem h1_norm_nonneg {f : FieldL2} (Df : H1Data f) : 0 ≤ Df.norm := Real.sqrt_nonneg _

theorem h1_field_norm_le {f : FieldL2} (Df : H1Data f) : ‖f‖ ≤ Df.norm := by
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem h1_derivative_norm_le {f : FieldL2} (Df : H1Data f) (j : Fin 3) :
    ‖Df.derivative j‖ ≤ Df.norm := by
  apply Real.le_sqrt_of_sq_le
  apply (Finset.single_le_sum (fun k _ => sq_nonneg ‖Df.derivative k‖) (Finset.mem_univ j)).trans
  exact le_add_of_nonneg_left (sq_nonneg ‖f‖)

def localH1Norm {f : FieldL2} (Df : H1Data f) (F : Finset Bloch.Alias) : ℝ :=
  Real.sqrt (‖familyProjection F f‖^2+∑ j : Fin 3, ‖familyProjection F (Df.derivative j)‖^2)

theorem separated_resolvent_localH1 {L z σ b N : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (F G : Finset Bloch.Alias) (hN : 0 ≤ N) (hF : (F.card : ℝ) ≤ N)
    (hG : (G.card : ℝ) ≤ N)
    (hsep : ∀ a ∈ F, ∀ c ∈ G, b ≤ paperCellDistance a c)
    {f : FieldL2} (Df : H1Data f) (hf : familyProjection G f = f)
    (hdf : ∀ j, familyProjection G (Df.derivative j) = Df.derivative j) :
    localH1Norm (resolventH1 D hσ0 hσ Df) F ≤ 4*boundaryCellMajorant L b N*Df.norm := by
  let M := boundaryCellMajorant L b N
  have hM : 0 ≤ M := boundaryCellMajorant_nonneg hN
  have hRn := separated_family_resolvent_norm hL D hσ0 hσ F G hN hF hG hsep
  have hR : ∀ u : FieldL2, familyProjection G u = u →
      ‖familyProjection F (resolvent D hσ0 hσ u)‖ ≤ M*‖u‖ := by
    intro u hu
    simpa only [ContinuousLinearMap.comp_apply, hu] using
      ((familyProjection F).comp ((resolvent D hσ0 hσ).comp (familyProjection G))).le_of_opNorm_le hRn u
  have hDn := separated_family_derivative_norm hL D hσ0 hσ F G hN hF hG hsep
  have hD : ∀ j, ‖familyProjection F (derivativeResolvent D hσ0 hσ j f)‖ ≤ M*‖f‖ := by
    intro j
    simpa only [ContinuousLinearMap.comp_apply, hf] using
      ((familyProjection F).comp ((derivativeResolvent D hσ0 hσ j).comp (familyProjection G))).le_of_opNorm_le (hDn j) f
  have hfield : ‖familyProjection F (resolvent D hσ0 hσ f)‖ ≤ M*Df.norm :=
    (hR f hf).trans (mul_le_mul_of_nonneg_left (h1_field_norm_le Df) hM)
  have hderiv (j : Fin 3) :
      ‖familyProjection F ((resolventH1 D hσ0 hσ Df).derivative j)‖ ≤ 2*(M*Df.norm) := by
    change ‖familyProjection F (resolvent D hσ0 hσ (Df.derivative j)+derivativeResolvent D hσ0 hσ j f)‖ ≤ _
    rw [map_add]
    apply (norm_add_le _ _).trans
    exact (add_le_add
      ((hR (Df.derivative j) (hdf j)).trans (mul_le_mul_of_nonneg_left (h1_derivative_norm_le Df j) hM))
      ((hD j).trans (mul_le_mul_of_nonneg_left (h1_field_norm_le Df) hM))).trans_eq (two_mul _).symm
  unfold localH1Norm
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hM) (h1_norm_nonneg Df)
  · have h0 : 0 ≤ M*Df.norm := mul_nonneg hM (h1_norm_nonneg Df)
    have hf2 := (sq_le_sq₀ (norm_nonneg _) h0).mpr hfield
    have hd2 : ∑ j : Fin 3, ‖familyProjection F ((resolventH1 D hσ0 hσ Df).derivative j)‖^2 ≤
        3*(2*(M*Df.norm))^2 := by
      calc
        _ ≤ ∑ _ : Fin 3, (2*(M*Df.norm))^2 := Finset.sum_le_sum fun j _ =>
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) h0)).mpr (hderiv j)
        _ = _ := by simp
    change ‖familyProjection F (resolvent D hσ0 hσ f)‖^2+_ ≤ (4*M*Df.norm)^2
    nlinarith only [hf2, hd2, sq_nonneg (M*Df.norm)]

#print axioms separated_resolvent_localH1

end Maxwell.Continuum.CellGauge
