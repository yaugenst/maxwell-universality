import Maxwell.Composition.ModeBaseline
import Maxwell.Composition.Bright

/-! Perturbation estimates on the actual repeated-mode orthogonal
complement, with no nontriviality assumption on that complement. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Maxwell.Composition
open scoped InnerProduct

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem sandwich_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (A : F →L[ℝ] G) (R : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (A.comp R)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖L‖ * (‖A‖ * ‖R‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = _ := by ring

theorem modePerturbation_upper (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) (hG : G.toLinearMap.IsSymmetric)
    (μ : ℝ) (heigen : G q = μ • q) (v : ι → ℝ)
    (E : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)) :
    ‖(blockInjection (ι := ι) q).adjoint.comp
      ((modeBaseline v G - E).comp (modeComplementInclusion (ι := ι) q))‖ ≤ ‖E‖ := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    modeBaseline_bright_complement_zero v G hG q μ heigen, zero_sub]
  exact (norm_neg ((blockInjection (ι := ι) q).adjoint.comp (E.comp (modeComplementInclusion (ι := ι) q)))).trans_le
    (sandwich_norm_le _ _ _ (modeAdjoint_norm_le q hq) (modeComplementInclusion_norm_le q))

theorem modePerturbation_lower (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ)
    (μ : ℝ) (heigen : G q = μ • q) (v : ι → ℝ)
    (E : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)) :
    ‖(modeComplementProjection (ι := ι) q).comp
      ((modeBaseline v G - E).comp (blockInjection (ι := ι) q))‖ ≤ ‖E‖ := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    modeBaseline_complement_bright_zero v G q hq μ heigen, zero_sub]
  exact (norm_neg ((modeComplementProjection (ι := ι) q).comp (E.comp (blockInjection (ι := ι) q)))).trans_le
    (sandwich_norm_le _ _ _ (modeComplementProjection_norm_le q) (modeInjection_norm_le q hq))

theorem modePerturbation_complement_inverse (q : EuclideanSpace ℝ κ)
    (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) (μ : ℝ)
    (A : ModeLocalComplement q ≃L[ℝ] ModeLocalComplement q)
    (hA : ∀ x : ModeLocalComplement q, (A x : EuclideanSpace ℝ κ) = μ • (x : EuclideanSpace ℝ κ) - G x)
    (g : ℝ) (hg : 0 < g)
    (hAi : ‖(A.symm : ModeLocalComplement q →L[ℝ] ModeLocalComplement q)‖ ≤ 1/g)
    (v : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (hv : ∀ i, |v i - μ| ≤ t)
    (E : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (hsmall : t + ‖E‖ ≤ g/2) :
    ∃ Dc : ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q,
      (Dc : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q) =
        (modeComplementProjection (ι := ι) q).comp ((modeBaseline v G - E).comp (modeComplementInclusion (ι := ι) q)) ∧
      ‖(Dc.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ ≤ 2/g := by
  let A0 := modeComplementBlockEquiv q (fun _ : ι => A)
  let Δ : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q :=
    modeComplementScalar q (fun i => v i - μ) -
      (modeComplementProjection (ι := ι) q).comp (E.comp (modeComplementInclusion (ι := ι) q))
  have hA0 : ‖(A0.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ ≤ 1/g :=
    modeComplementBlockEquiv_inverse_norm_le q (fun _ : ι => A) (1/g) (by positivity) (fun _ => hAi)
  have hΔ : ‖Δ‖ ≤ g/2 := by
    calc
      _ ≤ ‖modeComplementScalar q (fun i => v i - μ)‖ +
          ‖(modeComplementProjection (ι := ι) q).comp (E.comp (modeComplementInclusion (ι := ι) q))‖ :=
        norm_sub_le (modeComplementScalar q (fun i => v i - μ))
          ((modeComplementProjection (ι := ι) q).comp (E.comp (modeComplementInclusion (ι := ι) q)))
      _ ≤ t + ‖E‖ := add_le_add (modeComplementScalar_norm_le q _ t ht hv)
        (sandwich_norm_le _ _ _ (modeComplementProjection_norm_le q) (modeComplementInclusion_norm_le q))
      _ ≤ _ := hsmall
  have hprod : ‖(A0.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ * ‖Δ‖ ≤ 1/2 := by
    calc
      _ ≤ (1/g)*(g/2) := mul_le_mul hA0 hΔ (norm_nonneg Δ) (by positivity)
      _ = _ := by field_simp
  have hlt : ‖(A0.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ * ‖Δ‖ < 1 := by linarith
  refine ⟨perturbationEquiv A0 Δ hlt, ?_, ?_⟩
  · rw [perturbationEquiv_toContinuousLinearMap, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub, modeBaseline_complement v G q μ A hA]
    dsimp [A0, Δ]
    abel
  · have hden : (1/2 : ℝ) ≤ 1 - ‖(A0.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ * ‖Δ‖ := by linarith
    calc
      _ ≤ _ := perturbation_full_inverse_norm_le A0 Δ hlt
      _ ≤ (1/g)/(1/2) := div_le_div₀ (by positivity) hA0 (by norm_num) hden
      _ = _ := by ring

end Maxwell.Composition
