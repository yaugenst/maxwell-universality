import Maxwell.Continuum.BlochModulation
import Maxwell.Continuum.FreeFiberPotential

/-! The exact physical-phase / lattice-alias shift identity under the Bloch unitary. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory FourierTransform
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def fieldModulation (a : Space) : FieldL2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (modulation a).toContinuousLinearMap.comp (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) i))

@[simp] theorem fieldModulation_apply (a : Space) (u : FieldL2) (i : Fin 3) :
    fieldModulation a u i = modulation a (u i) := rfl

theorem fieldModulation_ae (a : Space) (u : FieldL2) (i : Fin 3) :
    fieldModulation a u i =ᵐ[volume] (fun x => phase a x * u i x) := modulation_ae a (u i)

def aliasFrequency (a : Alias) : Space := (1 / 2 : ℝ) • integerVector a

theorem frequencyJoin_sub_alias (q : QuasiCell) (n a : Alias) :
    quasiFrequencyJoin (q, n) - aliasFrequency a = quasiFrequencyJoin (q, n - a) := by
  apply PiLp.ext
  intro i
  simp only [PiLp.sub_apply, quasiFrequencyJoin_apply, aliasFrequency, PiLp.smul_apply,
    integerVector_apply, smul_eq_mul, Pi.sub_apply, Int.cast_sub]
  field_simp
  ring

def aliasShiftL2 (a : Alias) : FiberL2 →L[ℂ] FiberL2 :=
  (FreeFiber.shift a).compLpL 2 quasiMeasure

theorem aliasShiftL2_ae (a : Alias) (w : FiberL2) :
    aliasShiftL2 a w =ᵐ[quasiMeasure] (fun q => FreeFiber.shift a (w q)) :=
  (FreeFiber.shift a).coeFn_compLpL w

theorem fourier_fieldModulation_alias (a : Alias) (u : FieldL2) (i : Fin 3) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias,
      fieldFourier (fieldModulation (aliasFrequency a) u) i (quasiFrequencyJoin (q, n)) =
        fieldFourier u i (quasiFrequencyJoin (q, n - a)) := by
  have h := translation_ae (-aliasFrequency a) (𝓕 (u i))
  rw [← fourier_modulation] at h
  have hj := quasiFrequencyJoin_measurePreserving.quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [product_ae_all_alias hj] with q hq
  intro n
  have hn := hq n
  dsimp only [Function.comp_apply] at hn
  change 𝓕 (modulation (aliasFrequency a) (u i)) (quasiFrequencyJoin (q, n)) = _
  rw [hn, ← sub_eq_add_neg, frequencyJoin_sub_alias]
  rfl

/-- Multiplication by exp(iπ a·x) is exactly the lattice shift ν↦ν−a. -/
theorem unitary_fieldModulation (a : Alias) (u : FieldL2) :
    unitary (fieldModulation (aliasFrequency a) u) = aliasShiftL2 (-a) (unitary u) := by
  apply Lp.ext
  have h := ae_all_iff.mpr (fun i : Fin 3 => fourier_fieldModulation_alias a u i)
  filter_upwards [unitary_coordinate_ae (fieldModulation (aliasFrequency a) u),
    unitary_coordinate_ae u, aliasShiftL2_ae (-a) (unitary u), h]
      with q hmu hu hs hf
  rw [hs]
  apply lp.ext
  funext n
  apply PiLp.ext
  intro i
  change unitary (fieldModulation (aliasFrequency a) u) q n i = unitary u q (n + -a) i
  rw [hmu, hu, hf i n]
  rfl

end Maxwell.Continuum.Bloch
