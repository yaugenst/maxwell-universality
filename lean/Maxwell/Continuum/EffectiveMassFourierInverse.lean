import Maxwell.Continuum.FourierL1L2

/-! Literal inverse Fourier reconstruction for L¹∩L² amplitudes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum

open MeasureTheory FourierTransform

theorem fourierInv_integral_swap (f g : Space → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ Space)
    Real.continuous_fourierChar continuous_inner.neg hf hg
  have he : (-innerₗ Space).flip = -innerₗ Space := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  rw [he] at h
  exact h

theorem fourierInvL2_ae_integral (u : ScalarL2) (hu : Integrable (fun x => u x)) :
    (𝓕⁻ u : ScalarL2) =ᵐ[volume] 𝓕⁻ (fun x => u x) := by
  have hc : Continuous (𝓕⁻ (fun x => u x)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hu
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ u : ScalarL2)).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro φ hφ hs
  let ψ : SchwartzMap Space ℂ :=
    (hs.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hd := congrArg (fun T : ScalarDistribution => T ψ)
    (Lp.fourierInv_toTemperedDistribution_eq u)
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at hd
  have hswap := fourierInv_integral_swap (fun x => ψ x) (fun x => u x) ψ.integrable hu
  have he : (∫ x, ψ x * (𝓕⁻ u : ScalarL2) x) =
      ∫ x, ψ x * 𝓕⁻ (fun x => u x) x := by
    have hd' : (∫ x, ψ x * (𝓕⁻ u : ScalarL2) x) =
        ∫ x, 𝓕⁻ (fun x => ψ x) x * u x := by
      simpa only [smul_eq_mul, SchwartzMap.fourierInv_coe] using hd.symm
    exact hd'.trans hswap
  change (∫ x, (φ x : ℂ) * (𝓕⁻ u : ScalarL2) x) =
    ∫ x, (φ x : ℂ) * 𝓕⁻ (fun x => u x) x at he
  simpa only [Complex.real_smul, smul_eq_mul] using he

#print axioms fourierInvL2_ae_integral

end Maxwell.Continuum
