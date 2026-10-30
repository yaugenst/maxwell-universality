import Maxwell.Continuum.FiniteAuxiliaryTranslation
import Maxwell.Continuum.FourierTranslationCharacterization
import Mathlib.Analysis.Calculus.MeanValue

/-! H¹ algebra and translation estimates on the literal physical fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FourierSobolev

open Bloch MeasureTheory

theorem fieldTranslation_add (a b : Space) (f : FieldL2) :
    fieldTranslation a (fieldTranslation b f) = fieldTranslation (a+b) f :=
  congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (FiniteAuxiliary.translationOperator_add a b)

theorem fieldTranslation_comm (a b : Space) (f : FieldL2) :
    fieldTranslation a (fieldTranslation b f) = fieldTranslation b (fieldTranslation a f) := by
  rw [fieldTranslation_add, fieldTranslation_add, add_comm]

def H1Data.smul {f : FieldL2} (Df : H1Data f) (c : ℂ) : H1Data (c • f) where
  derivative j := c • Df.derivative j
  weak_derivative j k := by
    change partialDistribution j ((Lp.toTemperedDistributionCLM ℂ volume 2) (c • f k)) =
      (Lp.toTemperedDistributionCLM ℂ volume 2) (c • Df.derivative j k)
    rw [map_smul, map_smul, map_smul]
    exact congrArg (fun F : ScalarDistribution => c • F) (Df.weak_derivative j k)

def H1Data.add {f g : FieldL2} (Df : H1Data f) (Dg : H1Data g) : H1Data (f+g) where
  derivative j := Df.derivative j+Dg.derivative j
  weak_derivative j k := by
    change partialDistribution j ((Lp.toTemperedDistributionCLM ℂ volume 2) (f k+g k)) =
      (Lp.toTemperedDistributionCLM ℂ volume 2) (Df.derivative j k+Dg.derivative j k)
    rw [map_add, map_add, map_add]
    exact congrArg₂ (fun F G : ScalarDistribution => F+G) (Df.weak_derivative j k) (Dg.weak_derivative j k)

def H1Data.translate {f : FieldL2} (Df : H1Data f) (a : Space) : H1Data (fieldTranslation a f) where
  derivative j := fieldTranslation a (Df.derivative j)
  weak_derivative j := fieldWeakDerivative_of_translation_hasDerivAt j _ _ (by
    have he := (translationOperator a).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
      (Df.translation_hasDerivAt j)
    change HasDerivAt (fun t => fieldTranslation a (fieldTranslation (t • coordinateDirection j) f))
      (fieldTranslation a (Df.derivative j)) 0 at he
    simpa only [fieldTranslation_comm a] using he)

def h1Sum {ι : Type*} [Fintype ι] (f : ι → FieldL2) (D : ∀ i, H1Data (f i)) : H1Data (∑ i, f i) where
  derivative j := ∑ i, (D i).derivative j
  weak_derivative j k := by
    have hp (u : ι → FieldL2) : (∑ i, u i) k = ∑ i, u i k :=
      map_sum (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) k : FieldL2 →L[ℂ] ScalarL2) u Finset.univ
    rw [hp, hp]
    change partialDistribution j ((Lp.toTemperedDistributionCLM ℂ volume 2) (∑ i, f i k)) =
      (Lp.toTemperedDistributionCLM ℂ volume 2) (∑ i, (D i).derivative j k)
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun i _ => (D i).weak_derivative j k)

theorem H1Data.translation_hasDerivAt_at {f : FieldL2} (Df : H1Data f) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fieldTranslation (s • coordinateDirection j) f)
      (fieldTranslation (t • coordinateDirection j) (Df.derivative j)) t := by
  have h0 := (translationOperator (t • coordinateDirection j)).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0
    (Df.translation_hasDerivAt j)
  change HasDerivAt (fun s => fieldTranslation (t • coordinateDirection j)
      (fieldTranslation (s • coordinateDirection j) f))
    (fieldTranslation (t • coordinateDirection j) (Df.derivative j)) 0 at h0
  have ht := HasDerivAt.scomp_of_eq (x := t) h0 ((hasDerivAt_id t).sub_const t) (by simp)
  simp only [one_smul] at ht
  convert ht using 1
  funext s
  simp only [Function.comp_apply, id_eq]
  rw [fieldTranslation_add]
  apply congrArg (fun a : Space => fieldTranslation a f)
  module

theorem H1Data.coordinate_translation_bound {f : FieldL2} (Df : H1Data f) (j : Fin 3) (t : ℝ) :
    ‖fieldTranslation (t • coordinateDirection j) f-f‖ ≤ ‖Df.derivative j‖*|t| := by
  have hl : LipschitzWith ‖Df.derivative j‖₊ (fun t : ℝ => fieldTranslation (t • coordinateDirection j) f) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (Df.translation_hasDerivAt_at j t).differentiableAt)
    intro t
    rw [(Df.translation_hasDerivAt_at j t).deriv, (fieldTranslation _).nnnorm_map]
  simpa only [zero_smul, fieldTranslation_zero, sub_zero, Real.norm_eq_abs, coe_nnnorm] using hl.norm_sub_le t 0

#print axioms H1Data.coordinate_translation_bound
#print axioms h1Sum

end Maxwell.Continuum.FourierSobolev
