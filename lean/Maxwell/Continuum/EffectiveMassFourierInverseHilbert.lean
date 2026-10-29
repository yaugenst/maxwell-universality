import Maxwell.Continuum.EffectiveMassFourierInverse

/-! Vector-valued inverse Fourier reconstruction on the actual L²
space, including infinite-dimensional alias Hilbert spaces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum

open MeasureTheory FourierTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourierInv_integral_smul_swap (f : Space → ℂ) (g : Space → H)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x • g x) = ∫ x, f x • 𝓕⁻ g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ Space)
    Real.continuous_fourierChar continuous_inner.neg hf hg
  have he : (-innerₗ Space).flip = -innerₗ Space := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  rw [he] at h
  exact h

theorem fourierInvL2_ae_integral_hilbert (u : Lp H 2 (volume : Measure Space))
    (hu : Integrable (fun x => u x)) :
    (𝓕⁻ u : Lp H 2 (volume : Measure Space)) =ᵐ[volume] 𝓕⁻ (fun x => u x) := by
  have hc : Continuous (𝓕⁻ (fun x => u x)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg hu
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ u : Lp H 2 (volume : Measure Space))).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro φ hφ hs
  let ψ : SchwartzMap Space ℂ :=
    (hs.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hd := congrArg (fun T : TemperedDistribution Space H => T ψ)
    (Lp.fourierInv_toTemperedDistribution_eq u)
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at hd
  have hswap := fourierInv_integral_smul_swap (fun x => ψ x) (fun x => u x) ψ.integrable hu
  have he : (∫ x, ψ x • (𝓕⁻ u : Lp H 2 (volume : Measure Space)) x) =
      ∫ x, ψ x • 𝓕⁻ (fun x => u x) x := by
    have hd' : (∫ x, ψ x • (𝓕⁻ u : Lp H 2 (volume : Measure Space)) x) =
        ∫ x, 𝓕⁻ (fun x => ψ x) x • u x := by
      simpa only [SchwartzMap.fourierInv_coe] using hd.symm
    exact hd'.trans hswap
  change (∫ x, (φ x : ℂ) • (𝓕⁻ u : Lp H 2 (volume : Measure Space)) x) =
    ∫ x, (φ x : ℂ) • 𝓕⁻ (fun x => u x) x at he
  have hreal (r : ℝ) (v : H) : (r : ℂ) • v = r • v := by
    change (algebraMap ℝ ℂ r) • v = r • v
    exact algebraMap_smul ℂ r v
  simpa only [hreal] using he

#print axioms fourierInvL2_ae_integral_hilbert

end Maxwell.Continuum
