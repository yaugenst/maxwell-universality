import Maxwell.Continuum.BoxModesTensor
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The actual dense cosine algebra on a closed rectangular box

The three generators are `cos (π x_j / N_j)`. Their phases lie in `[0,π]`,
where cosine is injective, so they separate the actual box points.
Stone--Weierstrass therefore supplies density without assuming a Fourier
basis or a completeness premise.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open Set
open scoped BigOperators

/-- A compact coordinate presentation of the closed physical box. -/
abbrev ClosedCube (N : Fin 3 → ℝ) := (j : Fin 3) → Set.Icc (0 : ℝ) (N j)

/-- The canonical point of Euclidean space represented by box coordinates. -/
def cubePoint (N : Fin 3 → ℝ) (x : ClosedCube N) : Point :=
  WithLp.toLp 2 (fun j => (x j : ℝ))

@[simp] theorem cubePoint_apply (N : Fin 3 → ℝ) (x : ClosedCube N) (j : Fin 3) :
    cubePoint N x j = x j := rfl

theorem continuous_cubePoint (N : Fin 3 → ℝ) : Continuous (cubePoint N) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j))

def cubeCos (N : Fin 3 → ℝ) (n : ℤ) (j : Fin 3) : C(ClosedCube N, ℝ) where
  toFun x := intervalCos (N j) n (x j)
  continuous_toFun := (continuous_intervalCos (N j) n).comp
    (continuous_subtype_val.comp (continuous_apply j))

def cubeSin (N : Fin 3 → ℝ) (n : ℤ) (j : Fin 3) : C(ClosedCube N, ℝ) where
  toFun x := intervalSin (N j) n (x j)
  continuous_toFun := (continuous_intervalSin (N j) n).comp
    (continuous_subtype_val.comp (continuous_apply j))

/-- The concrete three-generator algebra; it is not defined by density. -/
def cosineAlgebra (N : Fin 3 → ℝ) : Subalgebra ℝ C(ClosedCube N, ℝ) :=
  Algebra.adjoin ℝ (Set.range (cubeCos N 1))

private theorem phase_mem_Icc (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (x : ClosedCube N) (j : Fin 3) :
    (Real.pi / N j) * (x j : ℝ) ∈ Set.Icc 0 Real.pi := by
  constructor
  · exact mul_nonneg (div_nonneg Real.pi_nonneg (hN j).le) (x j).property.1
  · calc
      (Real.pi / N j) * (x j : ℝ) ≤ (Real.pi / N j) * N j :=
        mul_le_mul_of_nonneg_left (x j).property.2
          (div_nonneg Real.pi_nonneg (hN j).le)
      _ = Real.pi := div_mul_cancel₀ _ (hN j).ne'

theorem cosineAlgebra_separatesPoints (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    (cosineAlgebra N).SeparatesPoints := by
  intro x y hxy
  have hcoord : ∃ j : Fin 3, x j ≠ y j := by
    by_contra h
    apply hxy
    funext j
    simp_all
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨_, ⟨cubeCos N 1 j, Algebra.subset_adjoin ⟨j, rfl⟩, rfl⟩, ?_⟩
  intro h
  apply hj
  apply Subtype.ext
  have hc : Real.cos (Real.pi / N j * (x j : ℝ)) =
      Real.cos (Real.pi / N j * (y j : ℝ)) := by
    simpa [cubeCos, intervalCos] using h
  have hp := Real.injOn_cos (phase_mem_Icc N hN x j) (phase_mem_Icc N hN y j) hc
  exact mul_left_cancel₀ (div_ne_zero Real.pi_ne_zero (hN j).ne') hp

/-- Concrete continuous-function density, proved from point separation. -/
theorem cosineAlgebra_dense (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j) :
    (cosineAlgebra N).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (cosineAlgebra N) (cosineAlgebra_separatesPoints N hN)

#print axioms cosineAlgebra_dense

end Maxwell.Continuum.BoxModes
