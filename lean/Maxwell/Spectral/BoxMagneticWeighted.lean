import Maxwell.Spectral.BoxMagnetic

/-! Weighted actual magnetic action remainder, retaining the sharper
bound on the weighted center curl. -/

noncomputable section

namespace Maxwell.Spectral.BoxMagneticWeighted

variable {E V G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedAddCommGroup G] [NormedSpace ℂ G]

def weightedAction (W : E →L[ℂ] G) (C D : E →L[ℂ] E) (A : V →L[ℂ] E) : V →L[ℂ] G :=
  W.comp (C.comp (D.comp A))

theorem weighted_remainder_identity
    (W : E →L[ℂ] G) (C C₁ δC D : E →L[ℂ] E) (A A₁ δA : V →L[ℂ] E) :
    weightedAction W (C + δC) D (A + δA) - weightedAction W C D A -
      (weightedAction W C₁ D A + weightedAction W C D A₁) =
    weightedAction W (δC - C₁) D A +
      weightedAction W C D (δA - A₁) + weightedAction W δC D δA := by
  simp only [weightedAction, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  module

private theorem norm_comp_of_bounds
    {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup C] [NormedSpace ℂ C]
    (T : B →L[ℂ] C) (S : A →L[ℂ] B) (a b : ℝ)
    (hT : ‖T‖ ≤ a) (hS : ‖S‖ ≤ b) : ‖T.comp S‖ ≤ a * b :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hT hS (norm_nonneg _) ((norm_nonneg _).trans hT))

/-- Exact source coefficient: weighting the center curl before estimating
the second remainder term preserves `curlmax` instead of replacing it by
the product of two separate operator norms. -/
theorem weighted_remainder_bound
    (W : E →L[ℂ] G) (C C₁ δC D : E →L[ℂ] E) (A A₁ δA : V →L[ℂ] E)
    (s ν e wmax curlmax : ℝ)
    (hW : ‖W‖ ≤ wmax) (hWC : ‖W.comp C‖ ≤ curlmax) (hD : ‖D‖ ≤ 1)
    (hA : ‖A‖ ≤ e) (hδC : ‖δC‖ ≤ s) (hremC : ‖δC - C₁‖ ≤ s ^ 2 / 2)
    (hδA : ‖δA‖ ≤ s * ν) (hremA : ‖δA - A₁‖ ≤ s ^ 2 * ν / 2) :
    ‖weightedAction W (C + δC) D (A + δA) - weightedAction W C D A -
      (weightedAction W C₁ D A + weightedAction W C D A₁)‖ ≤
        s ^ 2 * (wmax * e / 2 + (curlmax / 2 + wmax) * ν) := by
  have h₁ := norm_comp_of_bounds W ((δC - C₁).comp (D.comp A)) _ _ hW
    (norm_comp_of_bounds (δC - C₁) (D.comp A) _ _ hremC
      (norm_comp_of_bounds D A _ _ hD hA))
  have h₂ := norm_comp_of_bounds (W.comp C) (D.comp (δA - A₁)) _ _ hWC
    (norm_comp_of_bounds D (δA - A₁) _ _ hD hremA)
  have h₃ := norm_comp_of_bounds W (δC.comp (D.comp δA)) _ _ hW
    (norm_comp_of_bounds δC (D.comp δA) _ _ hδC
      (norm_comp_of_bounds D δA _ _ hD hδA))
  rw [weighted_remainder_identity]
  have hsum := (norm_add_le
    (weightedAction W (δC - C₁) D A + weightedAction W C D (δA - A₁))
    (weightedAction W δC D δA)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  change ‖weightedAction W (δC - C₁) D A‖ ≤ _ at h₁
  change ‖weightedAction W δC D δA‖ ≤ _ at h₃
  rw [ContinuousLinearMap.comp_assoc] at h₂
  change ‖weightedAction W C D (δA - A₁)‖ ≤ _ at h₂
  have heq : wmax * (s ^ 2 / 2 * (1 * e)) + curlmax * (1 * (s ^ 2 * ν / 2)) +
      wmax * (s * (1 * (s * ν))) =
      s ^ 2 * (wmax * e / 2 + (curlmax / 2 + wmax) * ν) := by ring
  linarith

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Momentum)
open BoxMagnetic

variable {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

/-- The weighted action of the actual Yee curl sandwich, with the
unchanged material inverse and the actual analytic first derivative. -/
theorem actual_weighted_remainder_bound
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ edge, 1 ≤ edgeAverage material edge) (c q : Momentum)
    (F : V' →L[ℂ] Field) (W : Field →L[ℂ] G) (ν e wmax curlmax : ℝ)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hW : ‖W‖ ≤ wmax) (hWC : ‖W.comp (curlOperator c)‖ ≤ curlmax) :
    ‖weightedAction W (curlOperator (c + q)) (inverseMaterial material) (appliedCurl (c + q) F) -
      weightedAction W (curlOperator c) (inverseMaterial material) (appliedCurl c F) -
      (weightedAction W (linearCurlOperator c q) (inverseMaterial material) (appliedCurl c F) +
        weightedAction W (curlOperator c) (inverseMaterial material) (appliedLinear c q F))‖ ≤
      displacementSize q ^ 2 * (wmax * e / 2 + (curlmax / 2 + wmax) * ν) := by
  have h := weighted_remainder_bound W (curlOperator c) (linearCurlOperator c q)
    (curlOperator (c + q) - curlOperator c) (inverseMaterial material)
    (appliedCurl c F) (appliedLinear c q F) (appliedIncrement c q F)
    (displacementSize q) ν e wmax curlmax hW hWC (inverseMaterial_norm material hm)
    hcenter (curlOperator_increment c q) (curlOperator_remainder c q)
    (appliedIncrement_norm c q F ν hF) (appliedRemainder_norm c q F ν hF)
  rw [show curlOperator c + (curlOperator (c + q) - curlOperator c) =
    curlOperator (c + q) by module, ← appliedCurl_add] at h
  exact h

theorem actual_weighted_remainder_bound_of_displacement
    (material : Maxwell.Spectral.PeriodicYee.Cell20 → ℝ)
    (hm : ∀ edge, 1 ≤ edgeAverage material edge) (c q : Momentum)
    (F : V' →L[ℂ] Field) (W : Field →L[ℂ] G) (s ν e wmax curlmax : ℝ)
    (hs : displacementSize q ≤ s) (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hW : ‖W‖ ≤ wmax) (hWC : ‖W.comp (curlOperator c)‖ ≤ curlmax) :
    ‖weightedAction W (curlOperator (c + q)) (inverseMaterial material) (appliedCurl (c + q) F) -
      weightedAction W (curlOperator c) (inverseMaterial material) (appliedCurl c F) -
      (weightedAction W (linearCurlOperator c q) (inverseMaterial material) (appliedCurl c F) +
        weightedAction W (curlOperator c) (inverseMaterial material) (appliedLinear c q F))‖ ≤
      s ^ 2 * (wmax * e / 2 + (curlmax / 2 + wmax) * ν) := by
  have hν : 0 ≤ ν := (norm_nonneg _).trans hF
  have he : 0 ≤ e := (norm_nonneg _).trans hcenter
  have hw : 0 ≤ wmax := (norm_nonneg _).trans hW
  have hc : 0 ≤ curlmax := (norm_nonneg _).trans hWC
  exact (actual_weighted_remainder_bound material hm c q F W ν e wmax curlmax
    hF hcenter hW hWC).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (displacementSize_nonneg q) hs 2)
        (by positivity))

end Maxwell.Spectral.BoxMagneticWeighted
