import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
import Maxwell.Spectral.YeeDerivatives

/-! The Schur quadratic jet obtained by differentiating the actual analytic
eigenpair equation.  The Hessian identity is a conclusion, not a premise. -/
namespace Maxwell.Spectral.EigenbranchJet

open Filter
open scoped Topology
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Twice differentiating evaluation of an analytic operator family. -/
theorem hasDerivAt_deriv_apply
    (A : ℂ → H →L[ℂ] H) (u : ℂ → H)
    (hA : AnalyticAt ℂ A 0) (hu : AnalyticAt ℂ u 0)
    (A1 A2 : H →L[ℂ] H) (u1 u2 : H)
    (hA1 : HasDerivAt A A1 0) (hA2 : HasDerivAt (deriv A) A2 0)
    (hu1 : HasDerivAt u u1 0) (hu2 : HasDerivAt (deriv u) u2 0) :
    HasDerivAt (deriv (fun t => A t (u t)))
      (A2 (u 0) + A1 u1 + (A1 u1 + A 0 u2)) 0 := by
  have heq : deriv (fun t => A t (u t)) =ᶠ[𝓝 (0 : ℂ)]
      fun t => deriv A t (u t) + A t (deriv u t) := by
    filter_upwards [hA.eventually_analyticAt, hu.eventually_analyticAt] with t hAt hut
    exact deriv_clm_apply hAt.differentiableAt hut.differentiableAt
  have hd := (hA2.clm_apply hu1).add (hA1.clm_apply hu2)
  rw [hA1.deriv, hu1.deriv] at hd
  exact HasDerivAt.congr_of_eventuallyEq hd heq

/-- Twice differentiating the eigenvalue times its analytic eigenvector. -/
theorem hasDerivAt_deriv_smul
    (value : ℂ → ℂ) (u : ℂ → H)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (v1 v2 : ℂ) (u1 u2 : H)
    (hv1 : HasDerivAt value v1 0) (hv2 : HasDerivAt (deriv value) v2 0)
    (hu1 : HasDerivAt u u1 0) (hu2 : HasDerivAt (deriv u) u2 0) :
    HasDerivAt (deriv (fun t => value t • u t))
      (value 0 • u2 + v1 • u1 + (v1 • u1 + v2 • u 0)) 0 := by
  have heq : deriv (fun t => value t • u t) =ᶠ[𝓝 (0 : ℂ)]
      fun t => value t • deriv u t + deriv value t • u t := by
    filter_upwards [hv.eventually_analyticAt, hu.eventually_analyticAt] with t hvt hut
    exact (hvt.differentiableAt.hasDerivAt.smul hut.differentiableAt.hasDerivAt).deriv
  have hd := (hv1.smul hu2).add (hv2.smul hu1)
  rw [hv1.deriv, hu1.deriv] at hd
  exact HasDerivAt.congr_of_eventuallyEq hd heq

/-- Local inversion symmetry forces the derivative of an analytic eigenvalue
to vanish at the center. -/
theorem deriv_zero_of_eventually_even (value : ℂ → ℂ)
    (heven : ∀ᶠ t in 𝓝 (0 : ℂ), value (-t) = value t) : deriv value 0 = 0 := by
  have heq : (fun t : ℂ => value (-t)) =ᶠ[𝓝 (0 : ℂ)] value := heven
  have he := heq.deriv_eq
  rw [deriv_comp_neg, neg_zero] at he
  linear_combination -(1 / 2 : ℂ) * he

/-- The exact second eigenvalue derivative follows from the eigenpair equation,
the unit center vector and the first corrector.  No second eigenvector
derivative or final Hessian expression is assumed. -/
theorem eigenvalue_second_derivative
    (A : ℂ → H →L[ℂ] H) (value : ℂ → ℂ) (u : ℂ → H)
    (hA : AnalyticAt ℂ A 0) (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ), A t (u t) = value t • u t)
    (energy : ℝ) (Φ Y : H) (A1 A2 : H →L[ℂ] H)
    (hv0 : value 0 = (energy : ℂ)) (hu0 : u 0 = Φ)
    (hunit : inner ℂ Φ Φ = 1) (hsym : (A 0).toLinearMap.IsSymmetric)
    (hA1 : HasDerivAt A A1 0) (hA2 : HasDerivAt (deriv A) ((2 : ℂ) • A2) 0)
    (hv1 : deriv value 0 = 0) (hu1 : deriv u 0 = -Y) :
    deriv (deriv value) 0 = (2 : ℂ) * inner ℂ Φ (A2 Φ - A1 Y) := by
  have hc : A 0 Φ = (energy : ℂ) • Φ := by
    simpa only [hu0, hv0] using hsolve.self_of_nhds
  have huv1 : HasDerivAt u (-Y) 0 := by simpa only [hu1] using hu.differentiableAt.hasDerivAt
  have hvv1 : HasDerivAt value 0 0 := by simpa only [hv1] using hv.differentiableAt.hasDerivAt
  have hf := hasDerivAt_deriv_apply A u hA hu A1 ((2 : ℂ) • A2) (-Y)
    (deriv (deriv u) 0) hA1 hA2 huv1 hu.deriv.differentiableAt.hasDerivAt
  have hg := hasDerivAt_deriv_smul value u hv hu 0 (deriv (deriv value) 0) (-Y)
    (deriv (deriv u) 0) hvv1 hv.deriv.differentiableAt.hasDerivAt
      huv1 hu.deriv.differentiableAt.hasDerivAt
  have heq : (fun t : ℂ => A t (u t)) =ᶠ[𝓝 (0 : ℂ)] (fun t => value t • u t) := hsolve
  have he := hf.unique (hg.congr_of_eventuallyEq heq.deriv)
  simp only [hu0, hv0, zero_smul, add_zero, zero_add, map_neg, _root_.smul_apply] at he
  have hi := congrArg (fun x : H => inner ℂ Φ x) he
  have hs : inner ℂ Φ (A 0 (deriv (deriv u) 0)) =
      (energy : ℂ) * inner ℂ Φ (deriv (deriv u) 0) := by
    have hh := hsym Φ (deriv (deriv u) 0)
    change inner ℂ (A 0 Φ) (deriv (deriv u) 0) = inner ℂ Φ (A 0 (deriv (deriv u) 0)) at hh
    rw [← hh, hc, inner_smul_left]
    simp
  simp only [inner_add_right, inner_smul_right, inner_neg_right, hs, hunit,
    mul_one, inner_sub_right] at hi ⊢
  linear_combination -hi

omit [CompleteSpace H] in
/-- Differentiating the fixed center normalization puts the derivative of the
constructed eigenvector in the orthogonal complement. -/
theorem eigenvector_derivative_orthogonal (u : ℂ → H) (hu : AnalyticAt ℂ u 0) (Φ : H)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ Φ (u t) = 1) :
    inner ℂ Φ (deriv u 0) = 0 := by
  have hd : HasDerivAt (fun t => inner ℂ Φ (u t)) (inner ℂ Φ (deriv u 0)) 0 :=
    (innerSL ℂ Φ).hasFDerivAt.comp_hasDerivAt 0 hu.differentiableAt.hasDerivAt
  have heq : (fun t => inner ℂ Φ (u t)) =ᶠ[𝓝 (0 : ℂ)] (fun _ => (1 : ℂ)) := hnorm
  exact hd.unique ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).congr_of_eventuallyEq heq)

omit [CompleteSpace H] in
/-- The first differentiated eigenpair equation identifies the derivative
with the exact corrector.  Uniqueness is required only on the fixed orthogonal
complement, precisely the simple-eigenvalue condition. -/
theorem eigenvector_derivative_eq_neg_corrector
    (A : ℂ → H →L[ℂ] H) (value : ℂ → ℂ) (u : ℂ → H)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ), A t (u t) = value t • u t)
    (energy : ℝ) (Φ Y : H) (A1 : H →L[ℂ] H)
    (hv0 : value 0 = (energy : ℂ)) (hu0 : u 0 = Φ)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ Φ (u t) = 1)
    (hA1 : HasDerivAt A A1 0) (hv1 : deriv value 0 = 0)
    (hY : inner ℂ Φ Y = 0)
    (hcancel : (A 0 - (energy : ℂ) • 1) Y = A1 Φ)
    (hsimple : ∀ v : H, inner ℂ Φ v = 0 → (A 0 - (energy : ℂ) • 1) v = 0 → v = 0) :
    deriv u 0 = -Y := by
  have heq : (fun t : ℂ => A t (u t)) =ᶠ[𝓝 (0 : ℂ)] (fun t => value t • u t) := hsolve
  have hf := hA1.clm_apply hu.differentiableAt.hasDerivAt
  have hg := hv.differentiableAt.hasDerivAt.smul hu.differentiableAt.hasDerivAt
  have he := hf.unique (HasDerivAt.congr_of_eventuallyEq hg heq)
  simp only [hu0, hv0, hv1, zero_smul, add_zero] at he
  have hd : A 0 (deriv u 0) = (energy : ℂ) • deriv u 0 - A1 Φ := by
    rw [← he]
    abel
  have hc : A 0 Y = A1 Φ + (energy : ℂ) • Y := by
    exact sub_eq_iff_eq_add.mp hcancel
  have horth : inner ℂ Φ (deriv u 0 + Y) = 0 := by
    rw [inner_add_right, eigenvector_derivative_orthogonal u hu Φ hnorm, hY, add_zero]
  have hker : (A 0 - (energy : ℂ) • 1) (deriv u 0 + Y) = 0 := by
    change A 0 (deriv u 0 + Y) - (energy : ℂ) • (deriv u 0 + Y) = 0
    rw [map_add, hd, hc, smul_add]
    abel
  exact eq_neg_iff_add_eq_zero.mpr (hsimple _ horth hker)

/-- Full normalized Schur-jet identity: inversion kills the linear eigenvalue
term and the simple complementary block identifies the corrector. -/
theorem eigenvalue_second_derivative_of_even_simple
    (A : ℂ → H →L[ℂ] H) (value : ℂ → ℂ) (u : ℂ → H)
    (hA : AnalyticAt ℂ A 0) (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ), A t (u t) = value t • u t)
    (energy : ℝ) (Φ Y : H) (A1 A2 : H →L[ℂ] H)
    (hv0 : value 0 = (energy : ℂ)) (hu0 : u 0 = Φ)
    (hsym : (A 0).toLinearMap.IsSymmetric)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ Φ (u t) = 1)
    (heven : ∀ᶠ t in 𝓝 (0 : ℂ), value (-t) = value t)
    (hA1 : HasDerivAt A A1 0) (hA2 : HasDerivAt (deriv A) ((2 : ℂ) • A2) 0)
    (hY : inner ℂ Φ Y = 0)
    (hcancel : (A 0 - (energy : ℂ) • 1) Y = A1 Φ)
    (hsimple : ∀ v : H, inner ℂ Φ v = 0 → (A 0 - (energy : ℂ) • 1) v = 0 → v = 0) :
    deriv (deriv value) 0 = (2 : ℂ) * inner ℂ Φ (A2 Φ - A1 Y) := by
  have hunit : inner ℂ Φ Φ = 1 := by simpa only [hu0] using hnorm.self_of_nhds
  have hv1 := deriv_zero_of_eventually_even value heven
  have hu1 := eigenvector_derivative_eq_neg_corrector A value u hv hu hsolve
    energy Φ Y A1 hv0 hu0 hnorm hA1 hv1 hY hcancel hsimple
  exact eigenvalue_second_derivative A value u hA hv hu hsolve energy Φ Y A1 A2
    hv0 hu0 hunit hsym hA1 hA2 hv1 hu1

open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.YeeTaylor Maxwell.Spectral.YeeAnalytic Maxwell.Spectral.YeeDerivatives

/-- The actual primitive Yee eigenbranch jet.  Operator analyticity, center
selfadjointness, and both directional derivative identities are all discharged
from the concrete stencil.  The eigenpair arguments are the normalized branch
constructed by the analytic implicit-function theorem. -/
theorem yee_eigenvalue_second_derivative
    (material : Cell20 → ℝ) (k q : Momentum)
    (value : ℂ → ℂ) (u : ℂ → EuclideanSpace ℂ Electric)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ t in 𝓝 (0 : ℂ),
      holomorphicOperator material k 0 (t • realMomentum q) (u t) = value t • u t)
    (energy : ℝ) (Φ Y : EuclideanSpace ℂ Electric)
    (hv0 : value 0 = (energy : ℂ)) (hu0 : u 0 = Φ)
    (hnorm : ∀ᶠ t in 𝓝 (0 : ℂ), inner ℂ Φ (u t) = 1)
    (heven : ∀ᶠ t in 𝓝 (0 : ℂ), value (-t) = value t)
    (hY : inner ℂ Φ Y = 0)
    (hcancel : (euclideanMap (PrimitiveYee.fiber material k) - (energy : ℂ) • 1) Y =
      shiftedOperatorCoefficient material k q 0 1 Φ)
    (hsimple : ∀ v : EuclideanSpace ℂ Electric, inner ℂ Φ v = 0 →
      (euclideanMap (PrimitiveYee.fiber material k) - (energy : ℂ) • 1) v = 0 → v = 0) :
    deriv (deriv value) 0 = (2 : ℂ) * inner ℂ Φ
      (shiftedOperatorCoefficient material k q 0 2 Φ - shiftedOperatorCoefficient material k q 0 1 Y) := by
  let A : ℂ → EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
    fun t => holomorphicOperator material k 0 (t • realMomentum q)
  have h0 : A 0 = euclideanMap (PrimitiveYee.fiber material k) := by
    simp [A, holomorphicOperator_zero]
  have hray : AnalyticAt ℂ (fun t : ℂ => t • realMomentum q) 0 :=
    analyticAt_id.smul analyticAt_const
  have hA : AnalyticAt ℂ A 0 :=
    (holomorphicOperator_analyticAt material k 0 0).comp_of_eq hray (by simp)
  have hsym : (A 0).toLinearMap.IsSymmetric := by
    rw [h0]
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    exact PrimitiveYee.fiber_hermitian material k
  apply eigenvalue_second_derivative_of_even_simple A value u hA hv hu hsolve
    energy Φ Y (shiftedOperatorCoefficient material k q 0 1)
    (shiftedOperatorCoefficient material k q 0 2) hv0 hu0 hsym hnorm heven
    (operator_hasDerivAt_center material k q 0)
    (operator_hasDerivAt_deriv_center material k q 0) hY
  · simpa only [h0] using hcancel
  · simpa only [h0] using hsimple

end
end Maxwell.Spectral.EigenbranchJet
