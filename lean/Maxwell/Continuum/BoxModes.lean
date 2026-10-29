import Maxwell.Continuum.ModeCount
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

/-!
# Explicit smooth PEC box Fourier modes

These are actual sine/cosine vector fields on Euclidean three-space.  Their
classical curl is computed by Fréchet differentiation, and their tangential
components vanish on the six box faces.  The curl-curl symbol is the concrete
matrix `|p|² I - p pᵀ`.

The results are pointwise smooth-field statements.  They do not claim that
these fields form a complete L² basis or identify the closed PEC curl domain;
those are separate analytical steps in the continuum operator construction.
-/

noncomputable section

namespace Maxwell.Continuum.BoxModes

open scoped BigOperators Matrix

abbrev Point := EuclideanSpace ℝ (Fin 3)
abbrev Vector := Fin 3 → ℝ
abbrev Field := Point → Vector

def direction (j : Fin 3) : Point := PiLp.single 2 j 1

/-- Literal Cartesian partial derivative of a scalar field. -/
def partialDeriv (f : Point → ℝ) (j : Fin 3) (x : Point) : ℝ :=
  fderiv ℝ f x (direction j)

/-- Literal Cartesian curl, with its conventional component signs. -/
def curl (E : Field) : Field := fun x =>
  ![partialDeriv (fun y => E y 2) 1 x - partialDeriv (fun y => E y 1) 2 x,
    partialDeriv (fun y => E y 0) 2 x - partialDeriv (fun y => E y 2) 0 x,
    partialDeriv (fun y => E y 1) 0 x - partialDeriv (fun y => E y 0) 1 x]

@[fun_prop] theorem differentiable_coordinate (j : Fin 3) :
    Differentiable ℝ (fun x : Point => x j) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).differentiable

@[simp] theorem partial_const (c : ℝ) (j : Fin 3) (x : Point) :
    partialDeriv (fun _ => c) j x = 0 := by
  simp [partialDeriv]

@[simp] theorem partial_coordinate (j k : Fin 3) (x : Point) :
    partialDeriv (fun y => y k) j x = if k = j then 1 else 0 := by
  change (fderiv ℝ (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : Point →L[ℝ] ℝ) x)
    (direction j) = _
  rw [ContinuousLinearMap.fderiv]
  simp [direction, PiLp.single_apply, eq_comm]

theorem partial_mul (f g : Point → ℝ) (j : Fin 3) (x : Point)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    partialDeriv (fun y => f y * g y) j x = f x * partialDeriv g j x + g x * partialDeriv f j x := by
  simp only [partialDeriv, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]

theorem partial_sin (f : Point → ℝ) (j : Fin 3) (x : Point)
    (hf : DifferentiableAt ℝ f x) :
    partialDeriv (fun y => Real.sin (f y)) j x = Real.cos (f x) * partialDeriv f j x := by
  simp only [partialDeriv, fderiv_sin hf, smul_apply, smul_eq_mul]

theorem partial_cos (f : Point → ℝ) (j : Fin 3) (x : Point)
    (hf : DifferentiableAt ℝ f x) :
    partialDeriv (fun y => Real.cos (f y)) j x = -Real.sin (f x) * partialDeriv f j x := by
  simp only [partialDeriv, fderiv_cos hf, smul_apply, smul_eq_mul]

/-- The component patterns with vanishing tangential trace on a box. -/
def electric (p a : Vector) : Field := fun x =>
  ![a 0 * Real.cos (p 0 * x 0) * Real.sin (p 1 * x 1) * Real.sin (p 2 * x 2),
    a 1 * Real.sin (p 0 * x 0) * Real.cos (p 1 * x 1) * Real.sin (p 2 * x 2),
    a 2 * Real.sin (p 0 * x 0) * Real.sin (p 1 * x 1) * Real.cos (p 2 * x 2)]

/-- The component pattern after one curl of an electric mode. -/
def magnetic (p b : Vector) : Field := fun x =>
  ![b 0 * Real.sin (p 0 * x 0) * Real.cos (p 1 * x 1) * Real.cos (p 2 * x 2),
    b 1 * Real.cos (p 0 * x 0) * Real.sin (p 1 * x 1) * Real.cos (p 2 * x 2),
    b 2 * Real.cos (p 0 * x 0) * Real.cos (p 1 * x 1) * Real.sin (p 2 * x 2)]


@[simp] theorem electric_zero (p : Vector) : electric p 0 = 0 := by
  funext x j
  fin_cases j <;> simp [electric]

@[simp] theorem magnetic_zero (p : Vector) : magnetic p 0 = 0 := by
  funext x j
  fin_cases j <;> simp [magnetic]

theorem electric_smul (p a : Vector) (c : ℝ) :
    electric p (c • a) = c • electric p a := by
  funext x j
  fin_cases j <;> simp [electric] <;> ring


/-- One curl changes the electric pattern into the magnetic pattern and acts
on the coefficient vector by the actual cross-product symbol. -/
theorem curl_electric (p a : Vector) : curl (electric p a) = magnetic p (p ⨯₃ a) := by
  funext x j
  fin_cases j <;>
    simp (disch := fun_prop) [curl, electric, magnetic, cross_apply,
      partial_mul, partial_sin, partial_cos] <;> ring

/-- The sign change in the second curl comes from differentiating cosines. -/
theorem curl_magnetic (p b : Vector) : curl (magnetic p b) = electric p (-(p ⨯₃ b)) := by
  funext x j
  fin_cases j <;>
    simp (disch := fun_prop) [curl, electric, magnetic, cross_apply,
      partial_mul, partial_sin, partial_cos] <;> ring

/-- The continuum curl-curl Fourier symbol, with no finite-grid dispersion. -/
def curlCurlSymbol (p a : Vector) : Vector :=
  fun j => (∑ k : Fin 3, p k ^ 2) * a j - p j * (∑ k : Fin 3, p k * a k)

theorem neg_cross_cross_eq_symbol (p a : Vector) :
    -(p ⨯₃ (p ⨯₃ a)) = curlCurlSymbol p a := by
  funext j
  fin_cases j <;> simp [cross_apply, curlCurlSymbol, Fin.sum_univ_succ] <;> ring

theorem curl_curl_electric (p a : Vector) :
    curl (curl (electric p a)) = electric p (curlCurlSymbol p a) := by
  rw [curl_electric, curl_magnetic, neg_cross_cross_eq_symbol]


/-- The Dirichlet scalar mode whose gradient is a longitudinal electric mode. -/
def scalarPotential (p : Vector) (x : Point) : ℝ :=
  Real.sin (p 0 * x 0) * Real.sin (p 1 * x 1) * Real.sin (p 2 * x 2)

/-- The zero block is populated by literal gradients, not by a declared
auxiliary vector subspace. -/
theorem gradient_scalarPotential (p : Vector) :
    (fun x j => partialDeriv (scalarPotential p) j x) = electric p p := by
  unfold scalarPotential
  funext x j
  fin_cases j <;>
    simp (disch := fun_prop) [electric, partial_mul, partial_sin] <;> ring


theorem curl_longitudinal (p : Vector) : curl (electric p p) = 0 := by
  rw [curl_electric, cross_self, magnetic_zero]

/-- Longitudinal coefficients generate exactly the zero eigenvalue. -/
theorem curlCurlSymbol_longitudinal (p : Vector) : curlCurlSymbol p p = 0 := by
  funext j
  simp [curlCurlSymbol, pow_two, mul_comm]

/-- Transverse coefficients have the positive eigenvalue `|p|²`. -/
theorem curlCurlSymbol_transverse (p a : Vector) (ha : ∑ j : Fin 3, p j * a j = 0) :
    curlCurlSymbol p a = (∑ j : Fin 3, p j ^ 2) • a := by
  funext j
  simp [curlCurlSymbol, ha]

/-- Literal pointwise positive-eigenmode equation for each transverse amplitude. -/
theorem curl_curl_electric_transverse (p a : Vector)
    (ha : ∑ j : Fin 3, p j * a j = 0) :
    curl (curl (electric p a)) = (∑ j : Fin 3, p j ^ 2) • electric p a := by
  rw [curl_curl_electric, curlCurlSymbol_transverse p a ha, electric_smul]

/-- Fixed physical box wave numbers. -/
def waveNumber (N : ModeCount.BoxLengths) (ν : Fin 3 → ℕ) : Vector :=
  fun j => Real.pi * (ν j : ℝ) / (N j : ℝ)

/-- At the lower face the two tangential electric components vanish. -/
theorem electric_tangential_lower (p a : Vector) (x : Point) (j k : Fin 3)
    (hjk : j ≠ k) (hx : x k = 0) : electric p a x j = 0 := by
  fin_cases j <;> fin_cases k <;> simp_all [electric]

/-- At the upper face the integer wave number gives the same exact PEC
condition; no small-boundary-error assumption is used. -/
theorem electric_tangential_upper (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)
    (ν : Fin 3 → ℕ) (a : Vector) (x : Point) (j k : Fin 3)
    (hjk : j ≠ k) (hx : x k = N k) : electric (waveNumber N ν) a x j = 0 := by
  have hsin : Real.sin (waveNumber N ν k * x k) = 0 := by
    rw [hx, waveNumber, div_mul_cancel₀]
    · simpa [mul_comm] using Real.sin_nat_mul_pi (ν k)
    · exact_mod_cast (Nat.ne_of_gt (hN k))
  fin_cases j <;> fin_cases k <;> simp_all [electric]

/-- The mode eigenvalue is exactly the free frequency counted in `ModeCount`. -/
theorem waveNumber_sq_sum (N : ModeCount.BoxLengths) (ν : Fin 3 → ℕ) :
    (∑ j : Fin 3, waveNumber N ν j ^ 2) = ModeCount.freeEigenvalue N ν := rfl

#print axioms curl_curl_electric
#print axioms gradient_scalarPotential
#print axioms electric_tangential_upper
#print axioms curlCurlSymbol_transverse

end Maxwell.Continuum.BoxModes
