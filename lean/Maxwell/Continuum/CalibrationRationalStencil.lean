import Maxwell.Continuum.CalibrationScaledFree
import Maxwell.Continuum.CalibrationComplementMaterial

/-! Executable rational free-block and material-stencil applications.
Complex Fourier values are represented by a pair of rational numbers;
all matrix actions use the same real rational entries on both parts. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

abbrev RationalComplex := ℚ × ℚ
abbrev RationalAliasField := Alias → Fin 3 → RationalComplex

noncomputable def rationalComplexLinear : RationalComplex →ₗ[ℚ] ℂ :=
  (Algebra.linearMap ℚ ℂ).comp (LinearMap.fst ℚ ℚ ℚ)+
    Complex.I • (Algebra.linearMap ℚ ℂ).comp (LinearMap.snd ℚ ℚ ℚ)

noncomputable def rationalComplexValue (z : RationalComplex) : ℂ := rationalComplexLinear z

theorem rationalComplexValue_eq (z : RationalComplex) :
    rationalComplexValue z = (z.1 : ℂ)+(z.2 : ℂ)*Complex.I := by
  change (z.1 : ℂ)+Complex.I*(z.2 : ℂ) = _
  ring

def Represents (f : RationalAliasField) (u : FiberSpace) : Prop :=
  ∀ ν j, rationalComplexValue (f ν j) = u ν j

def rationalNoncentral {V : Type*} [Zero V] (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν j => if rationalCentralCheck ν then 0 else f ν j

def rationalWeight (j : Fin 3) : ℚ := ![1/2,1,2] j

def rationalPotential {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν k => ∑ j : Fin 3, rationalWeight j • (f (ν+unitAlias j) k+f (ν-unitAlias j) k)

def rationalAmplitude : ℚ := (1/2)^100

def rationalPerturbation {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν j => -rationalAmplitude • rationalNoncentral (rationalPotential (rationalNoncentral f)) ν j

def rationalFreeApply {V : Type*} [AddCommMonoid V] [Module ℚ V]
    (t E : ℚ) (r : Fin 3 → ℚ) (f : Alias → Fin 3 → V) : Alias → Fin 3 → V :=
  fun ν i => ∑ j : Fin 3, rationalFreeInverseMatrix t E r ν i j • f ν j

theorem rationalWeight_cast (j : Fin 3) : (rationalWeight j : ℝ) = potentialWeight j := by
  fin_cases j <;> norm_num [rationalWeight, potentialWeight]

theorem rationalAmplitude_cast : (rationalAmplitude : ℝ) = backgroundAmplitude := by
  norm_num [rationalAmplitude, backgroundAmplitude]

theorem represents_noncentral {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalNoncentral f) (noncentralAliasProjection u) := by
  intro ν j
  rw [noncentralAliasProjection_apply]
  unfold rationalNoncentral
  by_cases hν : IsCentralAlias ν
  · have hb := (rationalCentralCheck_true ν).mpr hν
    simp only [hν, hb, ↓reduceIte]
    change rationalComplexLinear 0 = 0
    exact map_zero _
  · have hb : rationalCentralCheck ν = false := Bool.eq_false_iff.mpr
      (fun h => hν ((rationalCentralCheck_true ν).mp h))
    simp only [hν, hb, Bool.false_eq_true, ↓reduceIte]
    exact hf ν j

theorem represents_potential {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalPotential f) (potential u) := by
  intro ν k
  rw [potential_apply]
  change rationalComplexLinear (∑ j : Fin 3, rationalWeight j • (f (ν+unitAlias j) k+f (ν-unitAlias j) k)) = _
  simp only [map_sum, map_smul, map_add, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, PiLp.add_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]
  change (rationalWeight j : ℂ)*(rationalComplexValue (f (ν+unitAlias j) k)+
    rationalComplexValue (f (ν-unitAlias j) k)) = _
  rw [hf, hf]
  rw [← rationalWeight_cast]
  simp only [Complex.ofReal_ratCast, smul_eq_mul]

theorem represents_perturbation {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalPerturbation f) (calibrationMaterialPerturbation u) := by
  have hrep := represents_noncentral (represents_potential (represents_noncentral hf))
  intro ν j
  change rationalComplexLinear (-rationalAmplitude • rationalNoncentral
    (rationalPotential (rationalNoncentral f)) ν j) =
    (-(backgroundAmplitude : ℂ) • noncentralAliasProjection (potential (noncentralAliasProjection u))) ν j
  rw [map_smul]
  rw [← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul, Rat.cast_neg]
  change (-(rationalAmplitude : ℂ))*rationalComplexValue
    (rationalNoncentral (rationalPotential (rationalNoncentral f)) ν j) = _
  rw [hrep]
  simp only [lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← rationalAmplitude_cast]
  simp only [Complex.ofReal_ratCast]

theorem represents_freeApply (t E : ℚ) (r : Fin 3 → ℚ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/16) (ht : (3 : ℝ) ≤ t) (hE : (7 : ℝ) ≤ E ∧ (E : ℝ) ≤ 8)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalFreeApply t E r f) (scaledFreeInverse t E (fun j => (r j : ℝ)) hr ht hE u) := by
  intro ν i
  change rationalComplexLinear (∑ j : Fin 3, rationalFreeInverseMatrix t E r ν i j • f ν j) =
    scaledFreeInverseBlock t E (fun j => (r j : ℝ)) ν (u ν) i
  rw [scaledFreeInverseBlock_rational]
  simp only [map_sum, map_smul]
  simp_rw [← Rat.cast_smul_eq_qsmul ℂ, smul_eq_mul]
  change (∑ j : Fin 3, (rationalFreeInverseMatrix t E r ν i j : ℂ)*rationalComplexValue (f ν j)) =
    ∑ j : Fin 3, (rationalFreeInverseMatrix t E r ν i j : ℂ)*u ν j
  apply Finset.sum_congr rfl
  intro j _
  rw [hf]

#print axioms represents_freeApply
#print axioms represents_perturbation

end Maxwell.Continuum.Calibration
