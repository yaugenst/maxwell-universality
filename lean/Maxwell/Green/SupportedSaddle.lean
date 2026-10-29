import Maxwell.Green.SpectralLevelBody
import Maxwell.Green.AnalyticLocalGreen

/-! The actual imaginary support point supplies the principal-coordinate
simple-pole jet. All support geometry and transverse axes are constructed. -/

noncomputable section

namespace Maxwell.Green

open Filter Metric Set Complex
open scoped Topology ComplexConjugate InnerProductSpace

/-- Local spectral and numerator hypotheses produce the exact nonzero
residue and positive transverse saddle jet at every sufficiently small
energy level and every nonzero propagation direction. -/
theorem exists_supported_principal_saddle_within
    (lam A : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (hlam : AnalyticAt ℂ lam 0) (hA : AnalyticAt ℂ A 0) (hA₀ : A 0 ≠ 0)
    (hvalue : lam 0 = (edge : ℂ)) (hstationary : fderiv ℂ lam 0 = 0)
    (hpositive : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian lam 0 x x)
    (hreflection : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    {η : ℝ} (hη : 0 < η) :
    ∃ D : SpectralLevelBodyData lam edge, D.radius < η ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < D.quadraticConstant * D.radius ^ 2 →
      ∀ v : MomentumSpace, v ≠ 0 →
      ∃ (β : MomentumSpace) (χ : ℝ)
        (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : Fin 2 → ℝ),
        β ∈ ball (0 : MomentumSpace) D.radius ∧
        imaginaryMomentumLevel lam edge β = ξ ∧
        IsMaxOn (fun x => inner ℝ v x) (D.body ξ) β ∧ 0 < inner ℝ v β ∧
        0 < χ ∧ (∀ i, 0 < q i) ∧
        let center := I • momentumComplex β
        let T := principalChart (propagationNormal v) (b 0) (b 1)
        let F := affineDenominator lam center T ((edge - ξ : ℝ) : ℂ)
        let N := affineDenominator A center T 0
        AnalyticAt ℂ N 0 ∧ N 0 ≠ 0 ∧ AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧
        (fderiv ℂ F 0) (0, 1) = I * ((χ * ‖v‖ : ℝ) : ℂ) ∧
        (fderiv ℂ F 0).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0 ∧
        (∀ w : ℂ, -(2 : ℂ)⁻¹ * ((fderiv ℂ F 0) (0, 1))⁻¹ *
          (fderiv ℂ (fderiv ℂ F) 0) (realTransverse w, 0) (realTransverse w, 0) =
            quadraticPhase (χ * ‖v‖) (q 0) (q 1) w) := by
  let J : MomentumSpace →L[ℝ] ComplexTorusCoordinates := I • momentumComplexCLM
  have hJ₀ : J 0 = 0 := map_zero J
  have hnear : ∀ᶠ β : MomentumSpace in 𝓝 0,
      AnalyticAt ℂ A (J β) ∧ A (J β) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (J β), lam (reflectedComplexCoordinates z) = conj (lam z) := by
    have hc : Tendsto J (𝓝 (0 : MomentumSpace)) (𝓝 (0 : ComplexTorusCoordinates)) :=
      hJ₀ ▸ J.continuous.continuousAt.tendsto
    exact hc.eventually (hA.eventually_analyticAt.and
      ((hA.continuousAt.eventually_ne hA₀).and hreflection.eventually_nhds))
  obtain ⟨s, hs, hnears⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  obtain ⟨D, hD⟩ := exists_spectralLevelBodyData_within lam edge hlam hvalue hstationary
    hpositive (lt_min hη hs)
  have hDs : D.radius < s := hD.trans_le (min_le_right _ _)
  refine ⟨D, hD.trans_le (min_le_left _ _), ?_⟩
  intro ξ hξ hξr v hv
  obtain ⟨β, hβ, _⟩ := D.exists_unique_support_point hξ hξr v hv
  obtain ⟨χ, hχ, hg⟩ := hβ.2.2.2
  have hβclosed := ball_subset_closedBall hβ.1
  have hβs : β ∈ ball (0 : MomentumSpace) s :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hβ.1).trans hDs)
  obtain ⟨hAβ, hAβ₀, hreflectβ⟩ := hnears β hβs
  change AnalyticAt ℂ A (I • momentumComplex β) at hAβ
  change A (I • momentumComplex β) ≠ 0 at hAβ₀
  change ∀ᶠ z in 𝓝 (I • momentumComplex β),
    lam (reflectedComplexCoordinates z) = conj (lam z) at hreflectβ
  have hlamβ := D.local_analytic β hβclosed
  have hgradient : ∀ x : MomentumSpace,
      (fderiv ℂ lam (I • momentumComplex β)) (momentumComplex x) =
        I * (inner ℝ (χ • v) x : ℂ) := by
    intro x
    rw [← hg]
    exact imaginary_momentum_gradient_binding lam edge β _ hlamβ hreflectβ
      (D.hasStrictFDerivAt_gradient hβclosed).hasFDerivAt x
  have hBpositive : ∀ x : MomentumSpace, x ≠ 0 →
      0 < momentumHessian lam (I • momentumComplex β) x x := by
    intro x hx
    have hp : 0 < 2 * D.quadraticConstant * ‖x‖ ^ 2 := by
      exact mul_pos (mul_pos (by norm_num) D.quadraticConstant_pos)
        (sq_pos_of_pos (norm_pos_iff.mpr hx))
    exact hp.trans_le (D.hessian_lower β hβclosed x)
  obtain ⟨b, q, hq, hjet⟩ := exists_principal_saddle_jet lam (I • momentumComplex β)
    ((edge - ξ : ℝ) : ℂ) hlamβ v hv χ hχ (momentumHessian lam (I • momentumComplex β))
    (momentumHessian_symmetric lam _ hlamβ) hBpositive hgradient
    (imaginary_momentumHessian_binding lam β hlamβ hreflectβ)
  refine ⟨β, χ, b, q, hβ.1, hβ.2.1, hβ.2.2.1,
    D.support_pairing_pos hξ hξr hv hβ.2.2.1, hχ, hq, ?_⟩
  dsimp only
  refine ⟨affineDenominator_analytic hAβ _ 0, ?_, hjet.1, ?_, hjet.2⟩
  · simpa only [affineDenominator, map_zero, add_zero, sub_zero] using hAβ₀
  · simp only [affineDenominator, map_zero, add_zero,
      imaginary_momentum_on_level lam β edge ξ hreflectβ hβ.2.1, sub_self]


/-- The saddle construction on a previously fixed spectral body accepts
quantitative numerator information at the chosen energy, so the source
mode may be selected after that energy. -/
theorem exists_supported_principal_saddle_on
    (lam A : ComplexTorusCoordinates → ℂ) (edge : ℝ)
    (D : SpectralLevelBodyData lam edge) (ξ : ℝ) (hξ : 0 < ξ)
    (hξr : ξ < D.quadraticConstant * D.radius ^ 2)
    (hnum : ∀ β ∈ D.body ξ, AnalyticAt ℂ A (I • momentumComplex β) ∧
      A (I • momentumComplex β) ≠ 0)
    (hreflection : ∀ β ∈ D.body ξ, ∀ᶠ z in 𝓝 (I • momentumComplex β),
      lam (reflectedComplexCoordinates z) = conj (lam z)) :
      ∀ v : MomentumSpace, v ≠ 0 →
      ∃ (β : MomentumSpace) (χ : ℝ)
        (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : Fin 2 → ℝ),
        β ∈ ball (0 : MomentumSpace) D.radius ∧
        imaginaryMomentumLevel lam edge β = ξ ∧
        IsMaxOn (fun x => inner ℝ v x) (D.body ξ) β ∧ 0 < inner ℝ v β ∧
        0 < χ ∧ (∀ i, 0 < q i) ∧
        let center := I • momentumComplex β
        let T := principalChart (propagationNormal v) (b 0) (b 1)
        let F := affineDenominator lam center T ((edge - ξ : ℝ) : ℂ)
        let N := affineDenominator A center T 0
        AnalyticAt ℂ N 0 ∧ N 0 ≠ 0 ∧ AnalyticAt ℂ F 0 ∧ F 0 = 0 ∧
        (fderiv ℂ F 0) (0, 1) = I * ((χ * ‖v‖ : ℝ) : ℂ) ∧
        (fderiv ℂ F 0).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0 ∧
        (∀ w : ℂ, -(2 : ℂ)⁻¹ * ((fderiv ℂ F 0) (0, 1))⁻¹ *
          (fderiv ℂ (fderiv ℂ F) 0) (realTransverse w, 0) (realTransverse w, 0) =
            quadraticPhase (χ * ‖v‖) (q 0) (q 1) w) := by
  intro v hv
  obtain ⟨β, hβ, _⟩ := D.exists_unique_support_point hξ hξr v hv
  obtain ⟨χ, hχ, hg⟩ := hβ.2.2.2
  have hβclosed := ball_subset_closedBall hβ.1
  have hbody : β ∈ D.body ξ := ⟨hβclosed, hβ.2.1.le⟩
  obtain ⟨hAβ, hAβ₀⟩ := hnum β hbody
  have hreflectβ := hreflection β hbody
  change AnalyticAt ℂ A (I • momentumComplex β) at hAβ
  change A (I • momentumComplex β) ≠ 0 at hAβ₀
  change ∀ᶠ z in 𝓝 (I • momentumComplex β),
    lam (reflectedComplexCoordinates z) = conj (lam z) at hreflectβ
  have hlamβ := D.local_analytic β hβclosed
  have hgradient : ∀ x : MomentumSpace,
      (fderiv ℂ lam (I • momentumComplex β)) (momentumComplex x) =
        I * (inner ℝ (χ • v) x : ℂ) := by
    intro x
    rw [← hg]
    exact imaginary_momentum_gradient_binding lam edge β _ hlamβ hreflectβ
      (D.hasStrictFDerivAt_gradient hβclosed).hasFDerivAt x
  have hBpositive : ∀ x : MomentumSpace, x ≠ 0 →
      0 < momentumHessian lam (I • momentumComplex β) x x := by
    intro x hx
    have hp : 0 < 2 * D.quadraticConstant * ‖x‖ ^ 2 := by
      exact mul_pos (mul_pos (by norm_num) D.quadraticConstant_pos)
        (sq_pos_of_pos (norm_pos_iff.mpr hx))
    exact hp.trans_le (D.hessian_lower β hβclosed x)
  obtain ⟨b, q, hq, hjet⟩ := exists_principal_saddle_jet lam (I • momentumComplex β)
    ((edge - ξ : ℝ) : ℂ) hlamβ v hv χ hχ (momentumHessian lam (I • momentumComplex β))
    (momentumHessian_symmetric lam _ hlamβ) hBpositive hgradient
    (imaginary_momentumHessian_binding lam β hlamβ hreflectβ)
  refine ⟨β, χ, b, q, hβ.1, hβ.2.1, hβ.2.2.1,
    D.support_pairing_pos hξ hξr hv hβ.2.2.1, hχ, hq, ?_⟩
  dsimp only
  refine ⟨affineDenominator_analytic hAβ _ 0, ?_, hjet.1, ?_, hjet.2⟩
  · simpa only [affineDenominator, map_zero, add_zero, sub_zero] using hAβ₀
  · simp only [affineDenominator, map_zero, add_zero,
      imaginary_momentum_on_level lam β edge ξ hreflectβ hβ.2.1, sub_self]

end Maxwell.Green
