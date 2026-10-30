import Maxwell.Continuum.PECSupport
import Maxwell.Continuum.TranslationH1

/-! Locality of actual weak L² derivatives. This supplies compact support
of the differentiated auxiliary sources, not only support of the fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory TopologicalSpace
open scoped SchwartzMap

theorem partial_vanishes_open (Ω : Opens Space) (j : Fin 3) (f g : ScalarL2)
    (hd : partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g)
    (hf : ∀ᵐ x ∂volume, x ∈ Ω → f x = 0) :
    ∀ᵐ x ∂volume, x ∈ Ω → g x = 0 := by
  apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω)
  intro ψ hψ hψc hψs
  let φ : TestFunction Ω ℂ ⊤ :=
    ⟨fun x => (ψ x : ℂ), Complex.ofRealCLM.contDiff.comp hψ,
      hψc.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero),
      (tsupport_comp_subset (show Complex.ofReal 0 = 0 from Complex.ofReal_zero) ψ).trans hψs⟩
  have he := congrArg (fun F : ScalarDistribution => F (testSchwartz Ω φ)) hd
  simp only [partialDistribution, LineDeriv.lineDerivOpCLM_apply,
    TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply] at he
  have hz : ∫ x, partialSchwartz j (testSchwartz Ω φ) x • f x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with x hx
    change partialSchwartz j (testSchwartz Ω φ) x • f x = 0
    by_cases hΩ : x ∈ Ω
    · rw [hx hΩ, smul_zero]
    · have hzero : partialSchwartz j (testSchwartz Ω φ) x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        exact hΩ (φ.tsupport_subset
          ((SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection j) (testSchwartz Ω φ)) hs))
      rw [hzero, zero_smul]
  change (∫ x, -(partialSchwartz j (testSchwartz Ω φ) x) • f x) =
    ∫ x, (testSchwartz Ω φ) x • g x at he
  simp only [neg_smul, integral_neg] at he
  rw [hz, neg_zero] at he
  convert he.symm using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ψ x • g x = (ψ x : ℂ) • g x
    exact (IsScalarTower.algebraMap_smul ℂ (ψ x) (g x)).symm

theorem H1Data.derivative_vanishes_open {f : FieldL2} (Df : H1Data f)
    (Ω : Opens Space) (hf : ∀ k, ∀ᵐ x ∂volume, x ∈ Ω → f k x = 0) (j k : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ Ω → Df.derivative j k x = 0 :=
  partial_vanishes_open Ω j (f k) (Df.derivative j k) (Df.weak_derivative j k) (hf k)

theorem H1Data.derivative_supported_closed {f : FieldL2} (Df : H1Data f)
    {K : Set Space} (hK : IsClosed K)
    (hf : ∀ k, ∀ᵐ x ∂volume, x ∉ K → f k x = 0) (j k : Fin 3) :
    ∀ᵐ x ∂volume, x ∉ K → Df.derivative j k x = 0 :=
  Df.derivative_vanishes_open ⟨Kᶜ, hK.isOpen_compl⟩ hf j k

#print axioms H1Data.derivative_supported_closed

end Maxwell.Continuum.FourierSobolev
