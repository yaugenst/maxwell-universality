import Maxwell.Continuum.SchwartzCurlCommutator
import Maxwell.Continuum.SchwartzCellSupport

/-! A quantitative localized H¹ bound for the actual first-order
curl-curl commutator with a smooth cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.SchwartzMultiplier

open MeasureTheory CellGauge FourierSobolev

theorem secondProductRemainder_norm {C : ℝ} (hC : 0 ≤ C)
    (θ : SchwartzMap Space ℂ) (F : Finset Bloch.Alias)
    (hb₁ : ∀ j x, ‖partialSchwartz j θ x‖ ≤ C)
    (hb₂ : ∀ j k x, ‖partialSchwartz j (partialSchwartz k θ) x‖ ≤ C)
    (hs₁ : ∀ j x, cellIndex x ∉ F → partialSchwartz j θ x = 0)
    (hs₂ : ∀ j k x, cellIndex x ∉ F → partialSchwartz j (partialSchwartz k θ) x = 0)
    {f : FieldL2} (Df : H1Data f) (a b c : Fin 3) :
    ‖secondProductRemainder θ Df a b c‖ ≤ 3*C*localH1Norm Df F := by
  have h0 := (scalar_family_norm hC (partialSchwartz a (partialSchwartz b θ))
    (hb₂ a b) F (hs₂ a b) f c).trans
      (mul_le_mul_of_nonneg_left (localH1Norm_field Df F) hC)
  have h1 := (scalar_family_norm hC (partialSchwartz b θ) (hb₁ b) F (hs₁ b) (Df.derivative a) c).trans
    (mul_le_mul_of_nonneg_left (localH1Norm_derivative Df F a) hC)
  have h2 := (scalar_family_norm hC (partialSchwartz a θ) (hb₁ a) F (hs₁ a) (Df.derivative b) c).trans
    (mul_le_mul_of_nonneg_left (localH1Norm_derivative Df F b) hC)
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) h2)).trans_eq
    (by ring)

theorem curlCurlCommutator_norm {C : ℝ} (hC : 0 ≤ C)
    (θ : SchwartzMap Space ℂ) (F : Finset Bloch.Alias)
    (hb₁ : ∀ j x, ‖partialSchwartz j θ x‖ ≤ C)
    (hb₂ : ∀ j k x, ‖partialSchwartz j (partialSchwartz k θ) x‖ ≤ C)
    (hs₁ : ∀ j x, cellIndex x ∉ F → partialSchwartz j θ x = 0)
    (hs₂ : ∀ j k x, cellIndex x ∉ F → partialSchwartz j (partialSchwartz k θ) x = 0)
    {f : FieldL2} (Df : H1Data f) :
    ‖curlCurlCommutator θ Df‖ ≤ 24*C*localH1Norm Df F := by
  have hN := localH1Norm_nonneg Df F
  have hb := secondProductRemainder_norm hC θ F hb₁ hb₂ hs₁ hs₂ Df
  have hc (i : Fin 3) : ‖curlCurlCommutator θ Df i‖ ≤ 12*C*localH1Norm Df F := by
    exact ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (hb _ _ _) (hb _ _ _)))
      ((norm_sub_le _ _).trans (add_le_add (hb _ _ _) (hb _ _ _))))).trans_eq (by ring)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  have hs : ∑ i : Fin 3, ‖curlCurlCommutator θ Df i‖^2 ≤ 3*(12*C*localH1Norm Df F)^2 := by
    calc
      _ ≤ ∑ _ : Fin 3, (12*C*localH1Norm Df F)^2 := Finset.sum_le_sum fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hc i)
      _ = _ := by simp
  nlinarith only [hs, sq_nonneg (C*localH1Norm Df F)]

#print axioms curlCurlCommutator_norm

end Maxwell.Continuum.SchwartzMultiplier
