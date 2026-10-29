import Maxwell.Continuum.PeriodicBandQuadratic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! A concrete bilinear representation of the actual second Taylor
coefficient, and its coordinate-reflection symmetry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Filter
open scoped Topology

def bandBilinear : Momentum →L[ℂ] Momentum →L[ℂ] ℂ :=
  (continuousMultilinearCurryFin1 ℂ Momentum ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (bandSeries 2).curryLeft

theorem bandBilinear_apply (s t : Momentum) : bandBilinear s t = bandSeries 2 ![s, t] := by
  change bandSeries 2 (Fin.cons s (Fin.snoc 0 t)) = bandSeries 2 ![s, t]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem bandQuadratic_eq_bilinear (t : Momentum) : bandQuadratic t = bandBilinear t t := by
  rw [bandBilinear_apply]
  unfold bandQuadratic
  congr 1
  funext i
  fin_cases i <;> rfl

theorem reflection_smul (j : Fin 3) (c : ℂ) (t : Momentum) :
    FiberReflection.momentum j (c • t) = c • FiberReflection.momentum j t := by
  funext k
  simp only [FiberReflection.momentum, Pi.smul_apply, smul_eq_mul]
  ring

theorem bandQuadratic_reflect (t : Momentum) (j : Fin 3) :
    bandQuadratic (FiberReflection.momentum j t) = bandQuadratic t := by
  have hg : scaledSlice (FiberReflection.momentum j t) =ᶠ[𝓝 0] scaledSlice t := by
    filter_upwards [line_chart_eventually t] with z hz
    change scaledBand (z • FiberReflection.momentum j t) = scaledBand (z • t)
    rw [← reflection_smul]
    exact scaledBand_reflect hz j
  rw [bandQuadratic_eq_coefficient, bandQuadratic_eq_coefficient]
  unfold EvenTaylor.coefficient
  rw [hg.iteratedDeriv_eq 2]

def basisVector (j : Fin 3) : Momentum := Pi.single j 1

theorem basisVector_apply (j k : Fin 3) : basisVector j k = if k = j then 1 else 0 := by
  simp only [basisVector, Pi.single_apply]

theorem basis_expansion (t : Momentum) : t = ∑ j : Fin 3, t j • basisVector j := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem bandBilinear_expansion (t : Momentum) :
    bandQuadratic t = ∑ j : Fin 3, ∑ k : Fin 3,
      t j * t k * bandBilinear (basisVector j) (basisVector k) := by
  rw [bandQuadratic_eq_bilinear]
  calc
    bandBilinear t t = bandBilinear (∑ j : Fin 3, t j • basisVector j)
        (∑ k : Fin 3, t k • basisVector k) := congrArg₂ (fun u v => bandBilinear u v)
          (basis_expansion t) (basis_expansion t)
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem reflect_basis_same (j : Fin 3) : FiberReflection.momentum j (basisVector j) =
    -(basisVector j) := by
  funext k
  simp only [FiberReflection.momentum, FiberReflection.coordinateSign, basisVector_apply,
    Pi.neg_apply]
  split_ifs <;> norm_num

theorem reflect_basis_other (j k : Fin 3) (hjk : j ≠ k) :
    FiberReflection.momentum j (basisVector k) = basisVector k := by
  funext l
  simp only [FiberReflection.momentum, FiberReflection.coordinateSign, basisVector_apply]
  split_ifs <;> simp_all

theorem reflection_add (j : Fin 3) (s t : Momentum) :
    FiberReflection.momentum j (s + t) =
      FiberReflection.momentum j s + FiberReflection.momentum j t := by
  funext k
  simp only [FiberReflection.momentum, Pi.add_apply, mul_add]

theorem bandBilinear_cross_cancel (j k : Fin 3) (hjk : j ≠ k) :
    bandBilinear (basisVector j) (basisVector k) +
      bandBilinear (basisVector k) (basisVector j) = 0 := by
  have h := bandQuadratic_reflect (basisVector j + basisVector k) j
  rw [reflection_add, reflect_basis_same, reflect_basis_other j k hjk] at h
  simp only [bandQuadratic_eq_bilinear, map_add, map_neg, add_apply, neg_apply] at h
  linear_combination -(1 / 2 : ℂ) * h

end Maxwell.Continuum.PeriodicBand
