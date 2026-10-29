import Maxwell.Continuum.WeakCurl
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Actual bounded scalar dielectric multiplication

The multiplier is constructed from a measurable real coefficient on physical
three-space, using its literal pointwise product with L² representatives.
Neither the operator nor its continuity is supplied as an assumption.
-/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory
open scoped ComplexConjugate

/-- The material contract of the continuum construction. -/
structure ScalarDielectric where
  coefficient : Space → ℝ
  measurable : Measurable coefficient
  lower : ∀ x, 1 ≤ coefficient x
  upper : ∀ x, coefficient x ≤ 25

namespace ScalarDielectric

variable (ε : ScalarDielectric)

theorem coefficient_nonneg (x : Space) : 0 ≤ ε.coefficient x :=
  le_trans (by norm_num) (ε.lower x)

theorem coefficient_norm_le (x : Space) : ‖(ε.coefficient x : ℂ)‖ ≤ 25 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ε.coefficient_nonneg x)]
    using ε.upper x

theorem coefficient_aestronglyMeasurable :
    AEStronglyMeasurable (fun x => (ε.coefficient x : ℂ)) (volume : Measure Space) :=
  (Complex.continuous_ofReal.measurable.comp ε.measurable).aestronglyMeasurable

/-- Multiplication by the coefficient preserves actual L² integrability. -/
theorem scalarProduct_memLp (u : ScalarL2) :
    MemLp (fun x => (ε.coefficient x : ℂ) * u x) 2 (volume : Measure Space) := by
  apply (Lp.memLp u).of_le_mul (c := 25)
    (ε.coefficient_aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun x => by
    change ‖(ε.coefficient x : ℂ) * u x‖ ≤ 25 * ‖u x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ε.coefficient_norm_le x) (norm_nonneg _)

def scalarProduct (u : ScalarL2) : ScalarL2 :=
  (ε.scalarProduct_memLp u).toLp _

theorem scalarProduct_ae (u : ScalarL2) :
    ε.scalarProduct u =ᵐ[volume] fun x => (ε.coefficient x : ℂ) * u x :=
  MemLp.coeFn_toLp _

def scalarLinear : ScalarL2 →ₗ[ℂ] ScalarL2 where
  toFun := ε.scalarProduct
  map_add' u v := by
    apply Lp.ext
    filter_upwards [ε.scalarProduct_ae (u + v), ε.scalarProduct_ae u,
      ε.scalarProduct_ae v, Lp.coeFn_add u v,
      Lp.coeFn_add (ε.scalarProduct u) (ε.scalarProduct v)] with x hsum hu hv huv hprod
    rw [hsum, hprod, huv]
    simp only [Pi.add_apply, hu, hv]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [ε.scalarProduct_ae (c • u), ε.scalarProduct_ae u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (ε.scalarProduct u)] with x hc hu hcu hprod
    change ε.scalarProduct (c • u) x = (c • ε.scalarProduct u : ScalarL2) x
    rw [hc, hprod, hcu]
    simp only [Pi.smul_apply, hu, smul_eq_mul]
    ring

theorem scalarProduct_norm_le (u : ScalarL2) : ‖ε.scalarProduct u‖ ≤ 25 * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ε.scalarProduct_ae u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (ε.coefficient_norm_le x) (norm_nonneg _)

/-- The concrete continuous complex-linear scalar L² multiplier. -/
def scalarMultiplier : ScalarL2 →L[ℂ] ScalarL2 :=
  ε.scalarLinear.mkContinuous 25 ε.scalarProduct_norm_le

@[simp] theorem scalarMultiplier_apply (u : ScalarL2) :
    ε.scalarMultiplier u = ε.scalarProduct u := rfl

theorem scalarMultiplier_norm_le : ‖ε.scalarMultiplier‖ ≤ 25 :=
  ε.scalarLinear.mkContinuous_norm_le (by norm_num) ε.scalarProduct_norm_le

/-- The actual isotropic dielectric acts by the same scalar multiplication on
all three physical vector components. -/
def multiplier : FieldL2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ε.scalarMultiplier.comp (PiLp.proj 2 (fun _ : Fin 3 => ScalarL2) i))

@[simp] theorem multiplier_apply (u : FieldL2) (i : Fin 3) :
    ε.multiplier u i = ε.scalarMultiplier (u i) := rfl

theorem multiplier_ae (u : FieldL2) (i : Fin 3) :
    ε.multiplier u i =ᵐ[volume] fun x => (ε.coefficient x : ℂ) * u i x :=
  ε.scalarProduct_ae (u i)

theorem multiplier_apply_norm_le (u : FieldL2) : ‖ε.multiplier u‖ ≤ 25 * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (ε.scalarProduct_norm_le (u i))

theorem multiplier_norm_le : ‖ε.multiplier‖ ≤ 25 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ε.multiplier_apply_norm_le

/-- Support preservation is proved at the representative level. It does not
require the dielectric to preserve smooth functions. -/
theorem multiplier_vanishes_ae (Ω : Set Space) (u : FieldL2)
    (h : ∀ i, ∀ᵐ x ∂volume, x ∉ Ω → u i x = 0) :
    ∀ i, ∀ᵐ x ∂volume, x ∉ Ω → ε.multiplier u i x = 0 := by
  intro i
  filter_upwards [ε.multiplier_ae u i, h i] with x hx hu
  intro hout
  rw [hx, hu hout, mul_zero]

end ScalarDielectric
end Maxwell.Continuum
