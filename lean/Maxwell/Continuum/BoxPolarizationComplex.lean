import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Complex transverse coefficient fibers have at most two dimensions,
including fibers in which PEC admissibility removes some components. -/

noncomputable section

namespace Maxwell.Continuum.BoxPolarizationComplex

open scoped BigOperators

abbrev Vector := Fin 3 → ℂ

def divergence (p : Vector) : Vector →ₗ[ℂ] ℂ where
  toFun a := ∑ j : Fin 3, p j * a j
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' z a := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem divergence_apply (p a : Vector) : divergence p a = ∑ j, p j * a j := rfl

theorem divergence_surjective (p : Vector) (hp : p ≠ 0) :
    Function.Surjective (divergence p) := by
  classical
  have hcoord : ∃ j : Fin 3, p j ≠ 0 := by
    by_contra h
    apply hp
    funext j
    simp_all
  obtain ⟨j, hj⟩ := hcoord
  intro z
  refine ⟨Pi.single j (z / p j), ?_⟩
  simp [divergence, Pi.single_apply]
  field_simp

def transverse (p : Vector) : Submodule ℂ Vector := (divergence p).ker

theorem transverse_finrank (p : Vector) (hp : p ≠ 0) :
    Module.finrank ℂ (transverse p) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (divergence p)
  rw [LinearMap.range_eq_top.mpr (divergence_surjective p hp)] at h
  norm_num [Vector] at h
  change Module.finrank ℂ (divergence p).ker = 2
  omega

/-- Arbitrary additional component constraints can only reduce the number
of transverse polarizations. -/
theorem constrained_transverse_finrank_le (U : Submodule ℂ Vector) (p : Vector) (hp : p ≠ 0) :
    Module.finrank ℂ ↥(U ⊓ transverse p) ≤ 2 :=
  (Submodule.finrank_mono (show U ⊓ transverse p ≤ transverse p from inf_le_right)).trans_eq
    (transverse_finrank p hp)

def symbol (p : Vector) : Vector →ₗ[ℂ] Vector where
  toFun a j := (∑ k : Fin 3, p k ^ 2) * a j - p j * divergence p a
  map_add' a b := by
    funext j
    simp [map_add, mul_add]
    ring
  map_smul' z a := by
    funext j
    simp [map_smul]
    ring

theorem symbol_eigen_iff (p a : Vector) (hp : p ≠ 0) :
    symbol p a = (∑ k : Fin 3, p k ^ 2) • a ↔ a ∈ transverse p := by
  classical
  constructor
  · intro h
    have hcoord : ∃ j : Fin 3, p j ≠ 0 := by
      by_contra hzero
      apply hp
      funext j
      simp_all
    obtain ⟨j, hj⟩ := hcoord
    have he := congrFun h j
    change (∑ k, p k ^ 2) * a j - p j * divergence p a = (∑ k, p k ^ 2) * a j at he
    exact (mul_eq_zero.mp (sub_eq_self.mp he)).resolve_left hj
  · intro h
    funext j
    change (∑ k, p k ^ 2) * a j - p j * divergence p a = (∑ k, p k ^ 2) * a j
    change divergence p a = 0 at h
    rw [h, mul_zero, sub_zero]

theorem eigenspace_eq_transverse (p : Vector) (hp : p ≠ 0) :
    Module.End.eigenspace (symbol p) (∑ k : Fin 3, p k ^ 2) = transverse p := by
  ext a
  rw [Module.End.mem_eigenspace_iff]
  exact symbol_eigen_iff p a hp

end Maxwell.Continuum.BoxPolarizationComplex
