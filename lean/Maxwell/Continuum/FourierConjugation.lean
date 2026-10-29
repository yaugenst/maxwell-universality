import Maxwell.Continuum.BlochUnitary
import Maxwell.Continuum.PECDistribution

/-! Physical complex conjugation on actual scalar and vector L² spaces,
and its exact frequency-reversal identity for the Plancherel transform. -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory FourierTransform

def scalarConjugation : ScalarL2 →L[ℝ] ScalarL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

theorem scalarConjugation_ae (f : ScalarL2) :
    scalarConjugation f =ᵐ[volume] (fun x => star (f x)) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem scalarConjugation_involutive (f : ScalarL2) :
    scalarConjugation (scalarConjugation f) = f := by
  apply Lp.ext
  filter_upwards [scalarConjugation_ae (scalarConjugation f), scalarConjugation_ae f]
    with x h₁ h₂
  rw [h₁, h₂, star_star]

theorem scalarConjugation_toLp (f : SchwartzMap Space ℂ) :
    scalarConjugation (f.toLp 2) = (conjugateSchwartz f).toLp 2 := by
  apply Lp.ext
  filter_upwards [scalarConjugation_ae (f.toLp 2), f.coeFn_toLp 2,
    (conjugateSchwartz f).coeFn_toLp 2] with x hc hf hg
  rw [hc, hf, hg, conjugateSchwartz_apply]

def scalarReflection : ScalarL2 →ₗᵢ[ℂ] ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Space => -x) (Measure.measurePreserving_neg volume)

theorem scalarReflection_ae (f : ScalarL2) :
    scalarReflection f =ᵐ[volume] (fun x => f (-x)) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

theorem fourier_conjugate_schwartz (f : SchwartzMap Space ℂ) (ξ : Space) :
    𝓕 (conjugateSchwartz f) ξ = star (𝓕 f (-ξ)) := by
  change 𝓕 (fun x => conjugateSchwartz f x) ξ = star (𝓕 (fun x => f x) (-ξ))
  rw [Real.fourier_eq, Real.fourier_eq]
  change _ = starRingEnd ℂ (∫ x, Real.fourierChar (-inner ℝ x (-ξ)) • f x)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [conjugateSchwartz_apply, inner_neg_right, neg_neg, Circle.smul_def,
      smul_eq_mul, map_mul, Complex.star_def, ← Circle.coe_inv_eq_conj,
      AddChar.map_neg_eq_inv]

theorem fourier_scalarConjugation_schwartz (f : SchwartzMap Space ℂ) :
    𝓕 (scalarConjugation (f.toLp 2)) =
      scalarConjugation (scalarReflection (𝓕 (f.toLp 2))) := by
  rw [scalarConjugation_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  have hn := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp
    ((𝓕 f).coeFn_toLp 2)
  filter_upwards [(𝓕 (conjugateSchwartz f)).coeFn_toLp 2,
    scalarConjugation_ae (scalarReflection ((𝓕 f).toLp 2)),
    scalarReflection_ae ((𝓕 f).toLp 2), hn] with ξ hc hs hr hf
  dsimp only [Function.comp_apply] at hf
  rw [hc, hs, hr, hf]
  exact fourier_conjugate_schwartz f ξ

/-- Complex conjugation reverses frequency on all of L², by Schwartz density. -/
theorem fourier_scalarConjugation (f : ScalarL2) :
    𝓕 (scalarConjugation f) = scalarConjugation (scalarReflection (𝓕 f)) := by
  apply DenseRange.induction_on
    (p := fun f : ScalarL2 =>
      𝓕 (scalarConjugation f) = scalarConjugation (scalarReflection (𝓕 f)))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (continuous_fourier.comp scalarConjugation.continuous)
      (scalarConjugation.continuous.comp
        (scalarReflection.continuous.comp continuous_fourier))
  · exact fourier_scalarConjugation_schwartz

theorem fourier_scalarConjugation_ae (f : ScalarL2) :
    𝓕 (scalarConjugation f) =ᵐ[volume] (fun ξ => star (𝓕 f (-ξ))) := by
  rw [fourier_scalarConjugation]
  filter_upwards [scalarConjugation_ae (scalarReflection (𝓕 f)),
    scalarReflection_ae (𝓕 f)] with ξ hc hr
  rw [hc, hr]

def fieldConjugation : FieldL2 →L[ℝ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => scalarConjugation.comp
      (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) i))

@[simp] theorem fieldConjugation_apply (f : FieldL2) (i : Fin 3) :
    fieldConjugation f i = scalarConjugation (f i) := rfl

theorem fieldConjugation_involutive (f : FieldL2) :
    fieldConjugation (fieldConjugation f) = f := by
  apply PiLp.ext
  intro i
  exact scalarConjugation_involutive (f i)

theorem fieldFourier_conjugation_ae (f : FieldL2) (i : Fin 3) :
    fieldFourier (fieldConjugation f) i =ᵐ[volume]
      (fun ξ => star (fieldFourier f i (-ξ))) :=
  fourier_scalarConjugation_ae (f i)

end Maxwell.Continuum
