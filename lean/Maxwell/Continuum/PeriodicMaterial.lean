import Maxwell.Continuum.Material
import Maxwell.Continuum.FreeFiberNoncentral

/-! The literal physical scalar periodic medium, with its fixed contrast,
period and reflection symmetries proved pointwise. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicMaterial

open FreeFiber

def periodicPotential (x : Space) : ℝ :=
  Real.cos (Real.pi * x 0) + 2 * Real.cos (Real.pi * x 1) +
    4 * Real.cos (Real.pi * x 2)

theorem periodicPotential_continuous : Continuous periodicPotential := by
  have hc (j : Fin 3) : Continuous (fun x : Space => Real.cos (Real.pi * x j)) :=
    Real.continuous_cos.comp
      ((continuous_const : Continuous (fun _ : Space => Real.pi)).mul
        (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).continuous)
  exact ((hc 0).add (continuous_const.mul (hc 1))).add (continuous_const.mul (hc 2))

theorem periodicPotential_bounds (x : Space) :
    -7 ≤ periodicPotential x ∧ periodicPotential x ≤ 7 := by
  have h0 := Real.neg_one_le_cos (Real.pi * x 0)
  have h1 := Real.neg_one_le_cos (Real.pi * x 1)
  have h2 := Real.neg_one_le_cos (Real.pi * x 2)
  have h0' := Real.cos_le_one (Real.pi * x 0)
  have h1' := Real.cos_le_one (Real.pi * x 1)
  have h2' := Real.cos_le_one (Real.pi * x 2)
  unfold periodicPotential
  constructor <;> linarith

def coefficient (x : Space) : ℝ := 7 + backgroundAmplitude * periodicPotential x

theorem coefficient_bounds (x : Space) : 6 ≤ coefficient x ∧ coefficient x ≤ 8 := by
  obtain ⟨hlo, hhi⟩ := periodicPotential_bounds x
  have h1 := mul_le_mul_of_nonneg_left hlo backgroundAmplitude_pos.le
  have h2 := mul_le_mul_of_nonneg_left hhi backgroundAmplitude_pos.le
  have hρ := backgroundAmplitude_le
  unfold coefficient
  constructor <;> nlinarith

/-- The explicitly prescribed scalar material satisfies the global contract. -/
def dielectric : ScalarDielectric where
  coefficient := coefficient
  measurable := (continuous_const.add
    (continuous_const.mul periodicPotential_continuous)).measurable
  lower x := (by norm_num : (1 : ℝ) ≤ 6).trans (coefficient_bounds x).1
  upper x := (coefficient_bounds x).2.trans (by norm_num)

theorem dielectric_margin (x : Space) : dielectric.coefficient x ≤ 24 :=
  (coefficient_bounds x).2.trans (by norm_num)

/-- The real-space coefficients match the six-neighbor fiber weights. -/
theorem periodicPotential_sum (x : Space) :
    periodicPotential x = ∑ j : Fin 3,
      (2 * potentialWeight j) * Real.cos (Real.pi * x j) := by
  simp [periodicPotential, potentialWeight, Fin.sum_univ_succ]
  ring

def latticeTranslate (ν : Alias) (x : Space) : Space :=
  x + WithLp.toLp 2 (fun j => 2 * (ν j : ℝ))

theorem cosine_latticeTranslate (ν : Alias) (x : Space) (j : Fin 3) :
    Real.cos (Real.pi * latticeTranslate ν x j) = Real.cos (Real.pi * x j) := by
  change Real.cos (Real.pi * (x j + 2 * (ν j : ℝ))) = _
  have h : Real.pi * (x j + 2 * (ν j : ℝ)) =
      Real.pi * x j + (ν j : ℝ) * (2 * Real.pi) := by ring
  rw [h, Real.cos_add_int_mul_two_pi]

theorem periodicPotential_latticeTranslate (ν : Alias) (x : Space) :
    periodicPotential (latticeTranslate ν x) = periodicPotential x := by
  simp only [periodicPotential, cosine_latticeTranslate]

theorem dielectric_latticeTranslate (ν : Alias) (x : Space) :
    dielectric.coefficient (latticeTranslate ν x) = dielectric.coefficient x := by
  change 7 + backgroundAmplitude * periodicPotential (latticeTranslate ν x) = _
  rw [periodicPotential_latticeTranslate]
  rfl

def coordinateReflect (j : Fin 3) (x : Space) : Space :=
  WithLp.toLp 2 (fun k => if k = j then -x k else x k)

theorem cosine_coordinateReflect (j k : Fin 3) (x : Space) :
    Real.cos (Real.pi * coordinateReflect j x k) = Real.cos (Real.pi * x k) := by
  change Real.cos (Real.pi * (if k = j then -x k else x k)) = _
  by_cases h : k = j <;> simp [h, Real.cos_neg]

theorem periodicPotential_coordinateReflect (j : Fin 3) (x : Space) :
    periodicPotential (coordinateReflect j x) = periodicPotential x := by
  simp only [periodicPotential, cosine_coordinateReflect]

theorem dielectric_coordinateReflect (j : Fin 3) (x : Space) :
    dielectric.coefficient (coordinateReflect j x) = dielectric.coefficient x := by
  change 7 + backgroundAmplitude * periodicPotential (coordinateReflect j x) = _
  rw [periodicPotential_coordinateReflect]
  rfl

end Maxwell.Continuum.PeriodicMaterial
