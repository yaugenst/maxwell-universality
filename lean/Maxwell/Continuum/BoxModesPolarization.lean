import Maxwell.Continuum.BoxModes
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The two transverse polarizations of the continuum curl-curl symbol

This file computes the nullspace and positive eigenspace of the actual
three-component Fourier symbol from `BoxModes`.  In particular the factor two
in the free-mode count is proved by a finite-dimensional eigenspace argument,
not supplied as an assumed spectral multiplicity bound.
-/

noncomputable section

namespace Maxwell.Continuum.BoxModes

open scoped BigOperators Matrix

/-- The Fourier divergence functional. -/
def dotFunctional (p : Vector) : Vector →ₗ[ℝ] ℝ where
  toFun a := ∑ j : Fin 3, p j * a j
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem dotFunctional_apply (p a : Vector) :
    dotFunctional p a = ∑ j : Fin 3, p j * a j := rfl

/-- The curl-curl matrix as an actual linear endomorphism. -/
def curlCurlLinear (p : Vector) : Vector →ₗ[ℝ] Vector where
  toFun a := curlCurlSymbol p a
  map_add' a b := by
    funext j
    simp [curlCurlSymbol, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    funext j
    simp [curlCurlSymbol, Fin.sum_univ_succ]
    ring

@[simp] theorem curlCurlLinear_apply (p a : Vector) :
    curlCurlLinear p a = curlCurlSymbol p a := rfl

/-- Nonzero momentum defines a surjective divergence functional. -/
theorem dotFunctional_surjective (p : Vector) (hp : p ≠ 0) :
    Function.Surjective (dotFunctional p) := by
  have hcoord : ∃ j : Fin 3, p j ≠ 0 := by
    by_contra h
    apply hp
    funext j
    simp_all
  obtain ⟨j, hj⟩ := hcoord
  intro c
  refine ⟨Pi.single j (c / p j), ?_⟩
  simp [dotFunctional, Pi.single_apply]
  field_simp

/-- The two-dimensional transverse coefficient space. -/
def transverseSpace (p : Vector) : Submodule ℝ Vector := (dotFunctional p).ker

@[simp] theorem mem_transverseSpace (p a : Vector) :
    a ∈ transverseSpace p ↔ ∑ j : Fin 3, p j * a j = 0 := Iff.rfl

theorem finrank_transverseSpace (p : Vector) (hp : p ≠ 0) :
    Module.finrank ℝ (transverseSpace p) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotFunctional p)
  rw [LinearMap.range_eq_top.mpr (dotFunctional_surjective p hp)] at h
  norm_num [Vector] at h
  change Module.finrank ℝ (LinearMap.ker (dotFunctional p)) = 2
  omega

/-- At nonzero momentum the positive-symbol eigenvector equation is exactly
transversality. -/
theorem curlCurlSymbol_eigen_iff (p a : Vector) (hp : p ≠ 0) :
    curlCurlSymbol p a = (∑ j : Fin 3, p j ^ 2) • a ↔
      ∑ j : Fin 3, p j * a j = 0 := by
  constructor
  · intro h
    have hcoord : ∃ j : Fin 3, p j ≠ 0 := by
      by_contra h
      apply hp
      funext j
      simp_all
    obtain ⟨j, hj⟩ := hcoord
    have hjEq := congrFun h j
    simp only [curlCurlSymbol, Pi.smul_apply, smul_eq_mul] at hjEq
    exact (mul_eq_zero.mp (by linarith : p j * (∑ k : Fin 3, p k * a k) = 0)).resolve_left hj
  · exact curlCurlSymbol_transverse p a

/-- The positive eigenspace is the concrete transverse hyperplane. -/
theorem positive_eigenspace_eq_transverse (p : Vector) (hp : p ≠ 0) :
    Module.End.eigenspace (curlCurlLinear p) (∑ j : Fin 3, p j ^ 2) =
      transverseSpace p := by
  ext a
  rw [Module.End.mem_eigenspace_iff]
  exact curlCurlSymbol_eigen_iff p a hp

/-- The factor two in the free-space mode count, proved for the real symbol. -/
theorem finrank_positive_eigenspace (p : Vector) (hp : p ≠ 0) :
    Module.finrank ℝ
      (Module.End.eigenspace (curlCurlLinear p) (∑ j : Fin 3, p j ^ 2)) = 2 := by
  rw [positive_eigenspace_eq_transverse p hp, finrank_transverseSpace p hp]

/-- Positivity of the symbol energy is the squared cross-product identity. -/
theorem curlCurlSymbol_quadratic (p a : Vector) :
    (∑ j : Fin 3, a j * curlCurlSymbol p a j) =
      ∑ j : Fin 3, (p ⨯₃ a) j ^ 2 := by
  simp [curlCurlSymbol, cross_apply, Fin.sum_univ_succ]
  ring

theorem curlCurlSymbol_nonnegative (p a : Vector) :
    0 ≤ ∑ j : Fin 3, a j * curlCurlSymbol p a j := by
  rw [curlCurlSymbol_quadratic]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Symmetry is established directly for the same symbol used by the
pointwise differential identity. -/
theorem curlCurlSymbol_symmetric (p a b : Vector) :
    (∑ j : Fin 3, a j * curlCurlSymbol p b j) =
      ∑ j : Fin 3, curlCurlSymbol p a j * b j := by
  simp [curlCurlSymbol, Fin.sum_univ_succ]
  ring

#print axioms finrank_positive_eigenspace
#print axioms curlCurlSymbol_nonnegative

end Maxwell.Continuum.BoxModes
