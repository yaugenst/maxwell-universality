import Maxwell.Spectral.YeeTaylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Holomorphic continuation of the concrete centered primitive Yee fiber.
The formal adjoint conjugates the fixed stencil, never the complex momentum. -/
namespace Maxwell.Spectral.YeeAnalytic
noncomputable section
open Matrix
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor
open scoped Classical Matrix.Norms.L2Operator

abbrev ComplexMomentum := Direction → ℂ

def realMomentum (q : Momentum) : ComplexMomentum := fun j => (q j : ℂ)

def shiftCurl (k : Momentum) (j : Direction) : Matrix Electric Electric ℂ :=
  curlBlock (Pi.single j (PrimitiveYee.shift k j))

def identityCurl (j : Direction) : Matrix Electric Electric ℂ :=
  curlBlock (Pi.single j (1 : Matrix Cell Cell ℂ))

/-- Finite exponential stencil with fixed coefficient matrices. -/
def exponentialStencil (a : ℂ) (S T : Direction → Matrix Electric Electric ℂ)
    (z : ComplexMomentum) : Matrix Electric Electric ℂ :=
  ∑ j, (Complex.exp (a * z j) • S j - Complex.exp (-a * z j) • T j)

theorem exponentialStencil_analyticAt (a : ℂ) (S T : Direction → Matrix Electric Electric ℂ)
    (z : ComplexMomentum) : AnalyticAt ℂ (exponentialStencil a S T) z := by
  unfold exponentialStencil
  apply Finset.analyticAt_fun_sum
  intro j _
  have hj : AnalyticAt ℂ (fun w : ComplexMomentum => w j) z :=
    (ContinuousLinearMap.proj j : ComplexMomentum →L[ℂ] ℂ).analyticAt z
  have hpos : AnalyticAt ℂ (fun w : ComplexMomentum => Complex.exp (a * w j)) z :=
    (analyticAt_const.mul hj).cexp'
  have hneg : AnalyticAt ℂ (fun w : ComplexMomentum => Complex.exp (-a * w j)) z :=
    (analyticAt_const.mul hj).cexp'
  exact (hpos.smul analyticAt_const).sub (hneg.smul analyticAt_const)

/-- Actual centered curl, extended to complex Cartesian reciprocal momentum. -/
def holomorphicCurl (k : Momentum) : ComplexMomentum → Matrix Electric Electric ℂ :=
  exponentialStencil (Complex.I * (theta : ℂ)) (shiftCurl k) identityCurl

/-- Holomorphic formal adjoint. It agrees with the true adjoint on real
momentum, while retaining analytic dependence at complex momentum. -/
def holomorphicCurlAdjoint (k : Momentum) : ComplexMomentum → Matrix Electric Electric ℂ :=
  exponentialStencil (-Complex.I * (theta : ℂ))
    (fun j => (shiftCurl k j).conjTranspose) (fun j => (identityCurl j).conjTranspose)

def holomorphicFiber (material : Cell20 → ℝ) (k : Momentum)
    (z : ComplexMomentum) : Matrix Electric Electric ℂ :=
  holomorphicCurlAdjoint k z * holomorphicCurl k z - (1 / 64 : ℂ) • PrimitiveYee.mass material

theorem holomorphicCurl_analyticAt (k : Momentum) (z : ComplexMomentum) :
    AnalyticAt ℂ (holomorphicCurl k) z := exponentialStencil_analyticAt _ _ _ _

theorem holomorphicCurlAdjoint_analyticAt (k : Momentum) (z : ComplexMomentum) :
    AnalyticAt ℂ (holomorphicCurlAdjoint k) z := exponentialStencil_analyticAt _ _ _ _

theorem holomorphicFiber_analyticAt (material : Cell20 → ℝ) (k : Momentum)
    (z : ComplexMomentum) : AnalyticAt ℂ (holomorphicFiber material k) z :=
  ((holomorphicCurlAdjoint_analyticAt k z).mul (holomorphicCurl_analyticAt k z)).sub analyticAt_const

/-- On real momenta this exponential polynomial is precisely the actual
centered curl, including the primitive lattice boundary phases. -/
theorem holomorphicCurl_real (k q : Momentum) :
    holomorphicCurl k (realMomentum q) = centeredCurl k q := by
  ext ⟨i,p⟩ ⟨j,r⟩
  fin_cases i <;> fin_cases j <;>
    simp [holomorphicCurl, exponentialStencil, shiftCurl, identityCurl,
      centeredCurl, centeredDifference, curlBlock,
      Fin.sum_univ_three, realMomentum, mul_assoc]
  all_goals ring

theorem holomorphicCurlAdjoint_real (k q : Momentum) :
    holomorphicCurlAdjoint k (realMomentum q) = (centeredCurl k q).conjTranspose := by
  rw [← holomorphicCurl_real]
  simp only [holomorphicCurl, holomorphicCurlAdjoint, exponentialStencil,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
  apply Finset.sum_congr rfl
  intro j _
  have hp : star (Complex.exp ((Complex.I * (theta : ℂ)) * realMomentum q j)) =
      Complex.exp ((-Complex.I * (theta : ℂ)) * realMomentum q j) := by
    change starRingEnd ℂ (Complex.exp _) = _
    rw [← Complex.exp_conj]
    simp [realMomentum]
  have hn : star (Complex.exp (-(Complex.I * (theta : ℂ)) * realMomentum q j)) =
      Complex.exp (-(-Complex.I * (theta : ℂ)) * realMomentum q j) := by
    change starRingEnd ℂ (Complex.exp _) = _
    rw [← Complex.exp_conj]
    simp [realMomentum]
  rw [hp, hn]

theorem holomorphicFiber_real (material : Cell20 → ℝ) (k q : Momentum) :
    holomorphicFiber material k (realMomentum q) = centeredFiber material k q := by
  rw [holomorphicFiber, holomorphicCurlAdjoint_real, holomorphicCurl_real]
  rfl

/-- Holomorphic operator family for the finite-dimensional implicit-function
construction of the eigenbranch, including any fixed spectral shift. -/
def holomorphicOperator (material : Cell20 → ℝ) (k : Momentum) (E : ℝ)
    (z : ComplexMomentum) : EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  euclideanMap (holomorphicFiber material k z - (E : ℂ) • 1)

theorem holomorphicOperator_analyticAt (material : Cell20 → ℝ) (k : Momentum) (E : ℝ)
    (z : ComplexMomentum) : AnalyticAt ℂ (holomorphicOperator material k E) z :=
  (euclideanMap.analyticAt _).comp ((holomorphicFiber_analyticAt material k z).sub analyticAt_const)

theorem holomorphicOperator_real (material : Cell20 → ℝ) (k q : Momentum) (E : ℝ) :
    holomorphicOperator material k E (realMomentum q) = shiftedCenteredOperator material k q E := by
  rw [holomorphicOperator, holomorphicFiber_real]
  rfl

theorem holomorphicCurl_zero (k : Momentum) : holomorphicCurl k 0 = PrimitiveYee.curl k := by
  rw [show (0 : ComplexMomentum) = realMomentum 0 by rfl, holomorphicCurl_real]
  calc
    _ = curlCoefficient k 0 0 := by
      unfold centeredCurl curlCoefficient
      congr 1
      funext j
      simp [centeredDifference, differenceCoefficient]
    _ = _ := curlCoefficient_zero k 0

theorem holomorphicFiber_zero (material : Cell20 → ℝ) (k : Momentum) :
    holomorphicFiber material k 0 = PrimitiveYee.fiber material k := by
  have h := holomorphicCurlAdjoint_real k 0
  rw [← holomorphicCurl_real, show realMomentum 0 = (0 : ComplexMomentum) by rfl,
    holomorphicCurl_zero] at h
  rw [holomorphicFiber, h, holomorphicCurl_zero]
  rfl

theorem holomorphicOperator_zero (material : Cell20 → ℝ) (k : Momentum) (E : ℝ) :
    holomorphicOperator material k E 0 =
      euclideanMap (PrimitiveYee.fiber material k - (E : ℂ) • 1) := by
  rw [holomorphicOperator, holomorphicFiber_zero]

/-- The analytic continuation restricts to Hermitian physical fibers at real
momentum. This is a consequence of the concrete curl-square construction. -/
theorem holomorphicFiber_real_hermitian (material : Cell20 → ℝ) (k q : Momentum) :
    (holomorphicFiber material k (realMomentum q)).IsHermitian := by
  rw [holomorphicFiber_real]
  exact (Matrix.isHermitian_conjTranspose_mul_self _).sub
    ((PrimitiveYee.mass_hermitian material).smul (by
      change star (1 / 64 : ℂ) = (1 / 64 : ℂ)
      simp))

end
end Maxwell.Spectral.YeeAnalytic
