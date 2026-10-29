import Maxwell.Continuum.FreeFiberSelfAdjoint
import Mathlib.Tactic.GCongr

/-!
# Norm estimates for the literal complex Maxwell inverse

The rank-one numerator is estimated on all three polarizations. Momentum
squares remain bilinear, while all norms are the usual complex Hilbert norms.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

open scoped InnerProductSpace

def momentumVector (p : Momentum) : Polarization := WithLp.toLp 2 p

def conjugateVector (p : Momentum) : Polarization :=
  WithLp.toLp 2 (fun i => star (p i))

theorem conjugateVector_norm (p : Momentum) : ‖conjugateVector p‖ = ‖momentumVector p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, conjugateVector, momentumVector]

def bilinearDot (p q : Momentum) : ℂ := ∑ i, p i * q i

theorem bilinearDot_eq_inner (p q : Momentum) :
    bilinearDot p q = inner ℂ (conjugateVector p) (momentumVector q) := by
  simp [bilinearDot, PiLp.inner_apply, conjugateVector, momentumVector, mul_comm]

theorem bilinearDot_norm_le (p q : Momentum) :
    ‖bilinearDot p q‖ ≤ ‖momentumVector p‖ * ‖momentumVector q‖ := by
  rw [bilinearDot_eq_inner]
  simpa only [conjugateVector_norm] using norm_inner_le_norm (𝕜 := ℂ)
    (conjugateVector p) (momentumVector q)

theorem momentumSquare_norm_le (p : Momentum) :
    ‖momentumSquare p‖ ≤ ‖momentumVector p‖ ^ 2 := by
  simpa only [bilinearDot, momentumSquare, pow_two] using bilinearDot_norm_le p p

theorem momentumSquare_add (p q : Momentum) :
    momentumSquare (p + q) = momentumSquare p + 2 * bilinearDot p q + momentumSquare q := by
  simp only [momentumSquare, bilinearDot, Pi.add_apply, add_sq, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

theorem momentumSquare_add_error (p q : Momentum) :
    ‖momentumSquare (p + q) - momentumSquare p‖ ≤
      2 * ‖momentumVector p‖ * ‖momentumVector q‖ + ‖momentumVector q‖ ^ 2 := by
  rw [momentumSquare_add]
  have heq : momentumSquare p + 2 * bilinearDot p q + momentumSquare q - momentumSquare p =
      2 * bilinearDot p q + momentumSquare q := by ring
  rw [heq]
  calc
    ‖2 * bilinearDot p q + momentumSquare q‖ ≤
        ‖2 * bilinearDot p q‖ + ‖momentumSquare q‖ := norm_add_le _ _
    _ = 2 * ‖bilinearDot p q‖ + ‖momentumSquare q‖ := by rw [norm_mul]; norm_num
    _ ≤ 2 * (‖momentumVector p‖ * ‖momentumVector q‖) + ‖momentumVector q‖ ^ 2 := by
      gcongr
      · exact bilinearDot_norm_le p q
      · exact momentumSquare_norm_le q
    _ = _ := by ring

theorem momentumOuter_rankOne (p : Momentum) :
    matrixCLM (momentumOuter p) =
      InnerProductSpace.rankOne ℂ (momentumVector p) (conjugateVector p) := by
  apply ContinuousLinearMap.coe_injective
  change (momentumOuter p).toEuclideanLin =
    (InnerProductSpace.rankOne ℂ (momentumVector p) (conjugateVector p)).toLinearMap
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp [momentumOuter, Matrix.vecMulVec_apply, momentumVector, conjugateVector]

theorem momentumOuter_norm (p : Momentum) :
    ‖matrixCLM (momentumOuter p)‖ = ‖momentumVector p‖ ^ 2 := by
  rw [momentumOuter_rankOne, InnerProductSpace.norm_rankOne, conjugateVector_norm, pow_two]

theorem inverseBlock_eq_CLM (p : Momentum) (E : ℂ) :
    inverseBlock p E = (momentumSquare p - E)⁻¹ •
      (ContinuousLinearMap.id ℂ Polarization - E⁻¹ • matrixCLM (momentumOuter p)) := by
  simp only [inverseBlock, inverseMatrix, matrixCLM, map_smul, map_sub]
  congr 2
  ext v i
  exact congrArg (fun w : Polarization => w i) (matrixCLM_one v)

/-- A bound for the full inverse, including the longitudinal polarization. -/
theorem inverseBlock_norm_le (p : Momentum) (E : ℂ) :
    ‖inverseBlock p E‖ ≤
      ‖momentumSquare p - E‖⁻¹ * (1 + ‖E‖⁻¹ * ‖momentumVector p‖ ^ 2) := by
  rw [inverseBlock_eq_CLM, norm_smul, norm_inv]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
  calc
    ‖ContinuousLinearMap.id ℂ Polarization - E⁻¹ • matrixCLM (momentumOuter p)‖ ≤
        ‖ContinuousLinearMap.id ℂ Polarization‖ + ‖E⁻¹ • matrixCLM (momentumOuter p)‖ :=
      norm_sub_le _ _
    _ = 1 + ‖E‖⁻¹ * ‖momentumVector p‖ ^ 2 := by
      rw [ContinuousLinearMap.norm_id, norm_smul, norm_inv, momentumOuter_norm]

theorem momentumSquare_real (p : Fin 3 → ℝ) :
    momentumSquare (realMomentum p) = (‖momentumVector (realMomentum p)‖ ^ 2 : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [momentumSquare, realMomentum, momentumVector, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

end Maxwell.Continuum.FreeFiber
