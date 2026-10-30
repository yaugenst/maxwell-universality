import Maxwell.Continuum.CalibrationFiniteVector
import Maxwell.Continuum.CalibrationCachedExact

/-! The concrete output type for finite rational Fourier computations:
an explicit cube radius and a materialized array of rational pairs. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicSampling

structure FourierData where
  radius : ℕ
  coefficients : Vector RationalComplex (aliasArraySize radius)

namespace FourierData

def field (v : FourierData) : RationalAliasField := extendAliasArray v.radius v.coefficients

theorem supported (v : FourierData) : RationalSupported v.field v.radius := by
  intro ν hν j
  have hn : ¬aliasInCube v.radius ν := by
    intro h
    obtain ⟨k,hk⟩ := hν
    exact (not_lt_of_ge (h k)) hk
  simp only [field,extendAliasArray,hn,↓reduceDIte]

noncomputable def value (v : FourierData) : FiberSpace := representedFiber v.field v.supported

theorem represents (v : FourierData) : Represents v.field v.value := representedFiber_represents _ _

def ofSupported (f : RationalAliasField) (R : ℕ) : FourierData := ⟨R,sampleAliasArray R f⟩

theorem ofSupported_field {f : RationalAliasField} {R : ℕ} (hf : RationalSupported f R) :
    (ofSupported f R).field = f := extend_sample_supported hf

theorem ofSupported_represents {f : RationalAliasField} {R : ℕ} (hf : RationalSupported f R)
    {u : FiberSpace} (hu : Represents f u) : Represents (ofSupported f R).field u := by
  rw [ofSupported_field hf]
  exact hu

theorem ofSupported_value {f : RationalAliasField} {R : ℕ} (hf : RationalSupported f R)
    {u : FiberSpace} (hu : Represents f u) : (ofSupported f R).value = u :=
  represents_unique (ofSupported f R).represents (ofSupported_represents hf hu)

def normSq (v : FourierData) : ℚ := rationalNormSq v.field v.radius

theorem normSq_eq (v : FourierData) : (v.normSq : ℝ) = ‖v.value‖^2 :=
  rationalNormSq_eq v.supported v.represents

def scale (c : ℚ) (v : FourierData) : FourierData := ofSupported (c • v.field) v.radius

theorem scale_field (c : ℚ) (v : FourierData) : (scale c v).field = c • v.field :=
  ofSupported_field (v.supported.smul c)

theorem scale_value (c : ℚ) (v : FourierData) : (scale c v).value = (c : ℂ) • v.value :=
  ofSupported_value (v.supported.smul c) (represents_smul c v.represents)

def mass (v : FourierData) : ℚ :=
  ∑ ν ∈ Product.frequencyCube v.radius, ∑ j : Fin 3, (|(v.field ν j).1|+|(v.field ν j).2|)

theorem mass_nonneg (v : FourierData) : 0 ≤ v.mass := by unfold mass; positivity

theorem coefficient_norm_sum (v : FourierData) :
    (∑ ν ∈ Product.frequencyCube v.radius, ∑ j : Fin 3, ‖v.value ν j‖) ≤ (v.mass : ℝ) := by
  simp only [mass,Rat.cast_sum,Rat.cast_add,Rat.cast_abs]
  apply Finset.sum_le_sum
  intro ν _
  apply Finset.sum_le_sum
  intro j _
  rw [← v.represents ν j,rationalComplexValue_eq]
  have h := norm_add_le ((v.field ν j).1 : ℂ) (((v.field ν j).2 : ℂ)*Complex.I)
  simpa only [norm_mul,Complex.norm_I,mul_one,← Complex.ofReal_ratCast,
    Complex.norm_real,Real.norm_eq_abs] using h

#print axioms normSq_eq
#print axioms coefficient_norm_sum

end FourierData
end Maxwell.Continuum.Calibration
