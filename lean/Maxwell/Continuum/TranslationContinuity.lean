import Maxwell.Continuum.EffectiveMassAuxiliaryReality
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Strong continuity and physical reality of the actual L² translation
family, including its action on the Hermitian inner product. -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory

theorem scalarConjugation_inner (f g : ScalarL2) :
    inner ℂ (scalarConjugation f) (scalarConjugation g) = star (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def]
  change _ = starRingEnd ℂ (∫ x, inner ℂ (f x) (g x))
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [scalarConjugation_ae f, scalarConjugation_ae g] with x hf hg
  rw [hf, hg]
  change star (g x) * star (star (f x)) = star (g x * star (f x))
  rw [star_mul', star_star]

theorem fieldConjugation_inner (f g : FieldL2) :
    inner ℂ (fieldConjugation f) (fieldConjugation g) = star (inner ℂ f g) := by
  simp only [PiLp.inner_apply, fieldConjugation_apply, scalarConjugation_inner, star_sum]

theorem inner_im_zero_of_real {f g : FieldL2}
    (hf : fieldConjugation f = f) (hg : fieldConjugation g = g) :
    (inner ℂ f g).im = 0 := by
  have h := fieldConjugation_inner f g
  rw [hf, hg] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

namespace Bloch

theorem translation_continuous (f : ScalarL2) : Continuous (fun a : Space => translation a f) := by
  let g : Space → C(Space,Space) := fun a => ⟨fun x => x + a, continuous_id.add_const a⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact (continuous_const : Continuous (fun _ : Space => f)).compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right volume a) ENNReal.ofNat_ne_top

theorem fieldTranslation_continuous (f : FieldL2) :
    Continuous (fun a : Space => fieldTranslation a f) := by
  change Continuous (fun a : Space => WithLp.toLp 2 (fun j : Fin 3 => translation a (f j)))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ScalarL2)).comp
    (continuous_pi fun j => translation_continuous (f j))

theorem fieldTranslation_zero (f : FieldL2) : fieldTranslation 0 f = f := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  simpa only [add_zero] using fieldTranslation_ae 0 f j

theorem fieldTranslation_conjugation (a : Space) (f : FieldL2) :
    fieldTranslation a (fieldConjugation f) = fieldConjugation (fieldTranslation a f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (scalarConjugation_ae (f j))
  filter_upwards [fieldTranslation_ae a (fieldConjugation f) j,
    scalarConjugation_ae (fieldTranslation a f j), fieldTranslation_ae a f j, hp]
      with x ht hc hf hp
  dsimp only [Function.comp_apply] at hp
  change fieldTranslation a (fieldConjugation f) j x =
    scalarConjugation (fieldTranslation a f j) x
  rw [ht, fieldConjugation_apply, hp, hc, hf]

theorem fieldTranslation_preserves_real (a : Space) {f : FieldL2}
    (hf : fieldConjugation f = f) :
    fieldConjugation (fieldTranslation a f) = fieldTranslation a f := by
  rw [← fieldTranslation_conjugation, hf]

end Bloch
end Maxwell.Continuum
