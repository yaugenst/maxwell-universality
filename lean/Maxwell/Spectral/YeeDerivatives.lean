import Maxwell.Spectral.YeeAnalytic
import Maxwell.Spectral.YeeTaylorCoefficients
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual first and second derivatives of the holomorphic centered Yee
family, identified with the exact coefficients consumed by the certificates. -/
namespace Maxwell.Spectral.YeeDerivatives
noncomputable section
open Matrix
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor Maxwell.Spectral.YeeAnalytic
open Maxwell.Spectral.YeeTaylorCoefficients
open scoped Classical Matrix.Norms.L2Operator

/-- All directional derivatives of a finite exponential stencil. -/
def stencilJet (a : ℂ) (S T : Direction → Matrix Electric Electric ℂ)
    (q : ComplexMomentum) (n : ℕ) (t : ℂ) : Matrix Electric Electric ℂ :=
  ∑ j, (((a * q j)^n * Complex.exp ((a * q j) * t)) • S j -
    ((-a * q j)^n * Complex.exp ((-a * q j) * t)) • T j)

theorem exponential_jet_hasDerivAt (a : ℂ) (n : ℕ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => a^n * Complex.exp (a*s))
      (a^(n+1) * Complex.exp (a*t)) t := by
  simpa only [id_eq, mul_one, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).const_mul a).cexp).const_mul (a^n)

theorem stencilJet_hasDerivAt (a : ℂ) (S T : Direction → Matrix Electric Electric ℂ)
    (q : ComplexMomentum) (n : ℕ) (t : ℂ) :
    HasDerivAt (stencilJet a S T q n) (stencilJet a S T q (n+1) t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  exact ((exponential_jet_hasDerivAt _ n t).smul_const (S j)).sub
    ((exponential_jet_hasDerivAt _ n t).smul_const (T j))

theorem stencilJet_zero (a : ℂ) (S T : Direction → Matrix Electric Electric ℂ)
    (q : ComplexMomentum) (t : ℂ) :
    stencilJet a S T q 0 t = exponentialStencil a S T (t • q) := by
  simp [stencilJet, exponentialStencil, mul_comm, mul_left_comm]

def curlJet (k q : Momentum) (n : ℕ) (t : ℂ) : Matrix Electric Electric ℂ :=
  stencilJet (Complex.I * (theta : ℂ)) (shiftCurl k) identityCurl (realMomentum q) n t

def adjointCurlJet (k q : Momentum) (n : ℕ) (t : ℂ) : Matrix Electric Electric ℂ :=
  stencilJet (-Complex.I * (theta : ℂ))
    (fun j => (shiftCurl k j).conjTranspose) (fun j => (identityCurl j).conjTranspose)
    (realMomentum q) n t

theorem curlJet_zero (k q : Momentum) (t : ℂ) :
    curlJet k q 0 t = holomorphicCurl k (t • realMomentum q) := stencilJet_zero _ _ _ _ _

theorem adjointCurlJet_zero (k q : Momentum) (t : ℂ) :
    adjointCurlJet k q 0 t = holomorphicCurlAdjoint k (t • realMomentum q) :=
  stencilJet_zero _ _ _ _ _

theorem curlJet_hasDerivAt (k q : Momentum) (n : ℕ) (t : ℂ) :
    HasDerivAt (curlJet k q n) (curlJet k q (n+1) t) t := stencilJet_hasDerivAt _ _ _ _ _ _

theorem adjointCurlJet_hasDerivAt (k q : Momentum) (n : ℕ) (t : ℂ) :
    HasDerivAt (adjointCurlJet k q n) (adjointCurlJet k q (n+1) t) t :=
  stencilJet_hasDerivAt _ _ _ _ _ _

/-- Actual derivatives at the center equal factorial times the homogeneous
curl coefficients; no finite-difference derivative is used. -/
theorem curlJet_center (k q : Momentum) (n : ℕ) :
    curlJet k q n 0 = (n.factorial : ℂ) • curlCoefficient k q n := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  ext ⟨i,p⟩ ⟨j,r⟩
  fin_cases i <;> fin_cases j <;>
    simp [curlJet, stencilJet, shiftCurl, identityCurl, curlCoefficient,
      differenceCoefficient, curlBlock, Fin.sum_univ_three, realMomentum,
      mul_assoc]
  all_goals field_simp [hf]
  all_goals ring

theorem adjointCurlJet_center (k q : Momentum) (n : ℕ) :
    adjointCurlJet k q n 0 = (curlJet k q n 0).conjTranspose := by
  simp [adjointCurlJet, curlJet, stencilJet, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, realMomentum]

/-- The full first derivative, with the constant material disappearing by
ordinary differentiation of the actual holomorphic finite matrix. -/
def fiberJetOne (k q : Momentum) (t : ℂ) : Matrix Electric Electric ℂ :=
  adjointCurlJet k q 1 t * curlJet k q 0 t + adjointCurlJet k q 0 t * curlJet k q 1 t

theorem fiber_hasDerivAt (material : Cell20 → ℝ) (k q : Momentum) (t : ℂ) :
    HasDerivAt (fun s : ℂ => holomorphicFiber material k (s • realMomentum q))
      (fiberJetOne k q t) t := by
  have h := ((adjointCurlJet_hasDerivAt k q 0 t).mul (curlJet_hasDerivAt k q 0 t)).sub_const
    ((1 / 64 : ℂ) • PrimitiveYee.mass material)
  simpa only [Pi.mul_apply, Nat.zero_add, curlJet_zero, adjointCurlJet_zero, holomorphicFiber, fiberJetOne] using h

theorem fiberJetOne_hasDerivAt (k q : Momentum) (t : ℂ) :
    HasDerivAt (fiberJetOne k q)
      (adjointCurlJet k q 2 t * curlJet k q 0 t +
        adjointCurlJet k q 1 t * curlJet k q 1 t +
        (adjointCurlJet k q 1 t * curlJet k q 1 t +
          adjointCurlJet k q 0 t * curlJet k q 2 t)) t := by
  exact ((adjointCurlJet_hasDerivAt k q 1 t).mul (curlJet_hasDerivAt k q 0 t)).add
    ((adjointCurlJet_hasDerivAt k q 0 t).mul (curlJet_hasDerivAt k q 1 t))

theorem fiberJetOne_center (material : Cell20 → ℝ) (k q : Momentum) :
    fiberJetOne k q 0 = fiberCoefficient material k q 1 := by
  simp [fiberJetOne, adjointCurlJet_center, curlJet_center, curlCoefficient_zero,
    fiberCoefficient_one, add_comm]

theorem fiber_hasDerivAt_center (material : Cell20 → ℝ) (k q : Momentum) :
    HasDerivAt (fun s : ℂ => holomorphicFiber material k (s • realMomentum q))
      (fiberCoefficient material k q 1) 0 := by
  simpa only [fiberJetOne_center material] using fiber_hasDerivAt material k q 0

theorem fiber_hasDerivAt_deriv_center (material : Cell20 → ℝ) (k q : Momentum) :
    HasDerivAt (deriv (fun s : ℂ => holomorphicFiber material k (s • realMomentum q)))
      ((2 : ℂ) • fiberCoefficient material k q 2) 0 := by
  have hfun : deriv (fun s : ℂ => holomorphicFiber material k (s • realMomentum q)) =
      fiberJetOne k q := funext fun t => (fiber_hasDerivAt material k q t).deriv
  rw [hfun]
  convert fiberJetOne_hasDerivAt k q 0 using 1
  simp [adjointCurlJet_center, curlJet_center, curlCoefficient_zero,
    fiberCoefficient_two, Matrix.conjTranspose_smul]
  module

/-- The actual Euclidean operator family has this derivative along each
complex scalar multiple of a real physical momentum direction. -/
theorem operator_hasDerivAt (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q))
      (euclideanMap (fiberJetOne k q t)) t := by
  exact euclideanMap.hasFDerivAt.comp_hasDerivAt t
    ((fiber_hasDerivAt material k q t).sub_const ((E : ℂ) • 1))

/-- The certificate's actual linear coefficient is the first derivative. -/
theorem operator_hasDerivAt_center (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    HasDerivAt (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q))
      (shiftedOperatorCoefficient material k q E 1) 0 := by
  simpa only [fiberJetOne_center material, shiftedOperatorCoefficient, shiftedFiberCoefficient,
    Nat.one_ne_zero, ite_false, sub_zero] using operator_hasDerivAt material k q E 0

/-- Twice the certificate's actual quadratic coefficient is the second
derivative of the holomorphic finite Maxwell operator along the same ray. -/
theorem operator_hasDerivAt_deriv_center (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    HasDerivAt (deriv (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q)))
      ((2 : ℂ) • shiftedOperatorCoefficient material k q E 2) 0 := by
  have hfun : deriv (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q)) =
      fun t => euclideanMap (fiberJetOne k q t) :=
    funext fun t => (operator_hasDerivAt material k q E t).deriv
  rw [hfun]
  have hf := fiber_hasDerivAt_deriv_center material k q
  have hmatrix : deriv (fun s : ℂ => holomorphicFiber material k (s • realMomentum q)) =
      fiberJetOne k q := funext fun t => (fiber_hasDerivAt material k q t).deriv
  rw [hmatrix] at hf
  have hmap := euclideanMap.hasFDerivAt.comp_hasDerivAt 0 hf
  simpa only [shiftedOperatorCoefficient, shiftedFiberCoefficient,
    show (2 : ℕ) ≠ 0 by decide, ite_false, sub_zero, map_smul, Function.comp_def] using hmap

theorem deriv_operator_ray (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    deriv (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q)) 0 =
      shiftedOperatorCoefficient material k q E 1 :=
  (operator_hasDerivAt_center material k q E).deriv

theorem deriv_deriv_operator_ray (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    deriv (deriv (fun s : ℂ => holomorphicOperator material k E (s • realMomentum q))) 0 =
      (2 : ℂ) • shiftedOperatorCoefficient material k q E 2 :=
  (operator_hasDerivAt_deriv_center material k q E).deriv

end
end Maxwell.Spectral.YeeDerivatives
