import Maxwell.Continuum.FourierTranslationDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Exact equivalence between physical weak L² derivatives and strong
differentiation of the actual translation group. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory Bloch Filter
open scoped Topology

theorem weakDerivative_of_translation_hasDerivAt (j : Fin 3) (f g : ScalarL2)
    (hg : HasDerivAt (fun t : ℝ => translation (t • coordinateDirection j) f) g 0) :
    partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g := by
  have hz : translation (0 : Space) f = f := by
    apply Lp.ext
    simpa only [add_zero] using translation_ae 0 f
  obtain ⟨C, hC⟩ := hg.isBigO_sub.bound
  have hb : ∀ᶠ t : ℝ in 𝓝 0,
      ‖translation (t • coordinateDirection j) f-f‖ ≤ C*|t| := by
    simpa only [zero_smul, hz, sub_zero, Real.norm_eq_abs] using hC
  have hw := weakDerivative_distribution j f hb
  have he := hg.unique (translation_hasDerivAt j f (weakDerivative j f hb) hw)
  rw [he]
  exact hw

theorem weakDerivative_iff_translation_hasDerivAt (j : Fin 3) (f g : ScalarL2) :
    partialDistribution j (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g ↔
      HasDerivAt (fun t : ℝ => translation (t • coordinateDirection j) f) g 0 :=
  ⟨translation_hasDerivAt j f g, weakDerivative_of_translation_hasDerivAt j f g⟩

theorem H1Data.translation_hasDerivAt {f : FieldL2} (D : H1Data f) (j : Fin 3) :
    HasDerivAt (fun t : ℝ => fieldTranslation (t • coordinateDirection j) f) (D.derivative j) 0 := by
  have hp : HasDerivAt (fun t : ℝ => fun k : Fin 3 => translation (t • coordinateDirection j) (f k))
      (fun k => D.derivative j k) 0 :=
    hasDerivAt_pi.mpr fun k => FourierSobolev.translation_hasDerivAt j (f k)
      (D.derivative j k) (D.weak_derivative j k)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hp

theorem fieldWeakDerivative_of_translation_hasDerivAt (j : Fin 3) (f g : FieldL2)
    (hg : HasDerivAt (fun t : ℝ => fieldTranslation (t • coordinateDirection j) f) g 0) :
    ∀ k, partialDistribution j (Lp.toTemperedDistribution (f k)) = Lp.toTemperedDistribution (g k) := by
  intro k
  apply weakDerivative_of_translation_hasDerivAt j (f k) (g k)
  exact (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) k : FieldL2 →L[ℝ] ScalarL2).hasFDerivAt.comp_hasDerivAt 0 hg

#print axioms weakDerivative_iff_translation_hasDerivAt
#print axioms H1Data.translation_hasDerivAt

end Maxwell.Continuum.FourierSobolev
