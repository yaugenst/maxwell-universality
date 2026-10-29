import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Disjoint Euclidean block modes

Injection and readout use actual finite coordinate arrays. Their norm and
calibration bounds contain no factor depending on the number of blocks.
-/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators InnerProduct

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Insert the same local mode into each disjoint defect block. -/
def blockInjectionLinear (q : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun g := WithLp.toLp 2 (fun ij => q ij.2 * g ij.1)
  map_add' g h := by ext ij; simp [mul_add]
  map_smul' a g := by ext ij; simp [mul_left_comm]

/-- Disjoint supports give an exact tensor-product norm identity. -/
theorem blockInjectionLinear_norm (q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖blockInjectionLinear q g‖ = ‖q‖ * ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [blockInjectionLinear, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
    Fintype.sum_prod_type, mul_pow]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]

/-- The actual bounded linear block injection. -/
def blockInjection (q : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  LinearMap.toContinuousLinearMap (blockInjectionLinear (ι := ι) q)

@[simp] theorem blockInjection_apply (q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι)
    (i : ι) (j : κ) : blockInjection q g (i, j) = q j * g i := rfl

theorem blockInjection_norm_apply (q : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖blockInjection q g‖ = ‖q‖ * ‖g‖ := blockInjectionLinear_norm q g

theorem blockInjection_norm_le (q : EuclideanSpace ℝ κ) :
    ‖(blockInjection q : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ))‖ ≤ ‖q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g =>
    (blockInjection_norm_apply q g).le)

@[simp] theorem blockInjection_sub (qhat q : EuclideanSpace ℝ κ) :
    (blockInjection qhat - blockInjection q :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ)) = blockInjection (qhat - q) := by
  ext g ij
  simp only [sub_apply, PiLp.sub_apply]
  exact (sub_mul _ _ _).symm

/-- Calibration of the one local mode controls the complete injection. -/
theorem blockInjection_calibration (qhat q : EuclideanSpace ℝ κ) :
    ‖(blockInjection qhat - blockInjection q :
      EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ))‖ ≤ ‖qhat - q‖ := by
  rw [blockInjection_sub]
  exact blockInjection_norm_le _

/-- A genuine diagonal map on the block coefficient space. -/
def blockDiagonal (v : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => WithLp.toLp 2 (fun i => v i * g i)
      map_add' := by intros; ext i; simp [mul_add]
      map_smul' := by intros; ext i; simp [mul_left_comm] }

@[simp] theorem blockDiagonal_apply (v : ι → ℝ) (g : EuclideanSpace ℝ ι) (i : ι) :
    blockDiagonal v g i = v i * g i := rfl

theorem blockDiagonal_norm_le (v : ι → ℝ) (vmax : ℝ)
    (hvmax : 0 ≤ vmax) (hv : ∀ i, |v i| ≤ vmax) : ‖blockDiagonal v‖ ≤ vmax := by
  apply ContinuousLinearMap.opNorm_le_bound _ hvmax
  intro g
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hvmax (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [blockDiagonal_apply, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h := (sq_le_sq₀ (abs_nonneg (v i)) hvmax).mpr (hv i)
  simpa only [sq_abs] using h

/-- Local-mode readout with one signed strength per defect. -/
def blockReadout (q : EuclideanSpace ℝ κ) (v : ι → ℝ) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ ι :=
  (blockDiagonal v).comp (blockInjection q).adjoint

/-- The adjoint definition has precisely the stated local dot-product
implementation. No global solve occurs in readout. -/
theorem blockReadout_apply (q : EuclideanSpace ℝ κ) (v : ι → ℝ)
    (y : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    blockReadout q v y i = v i * ∑ j, q j * y (i, j) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (blockInjection q)
    (EuclideanSpace.single i 1) y
  simp [PiLp.inner_apply, Fintype.sum_prod_type, blockInjection_apply, mul_comm] at h
  simpa [blockReadout] using congrArg (fun t : ℝ => v i * t) h

/-- The complete readout norm depends on local mode size and the maximum
strength, not the number of defects. -/
theorem blockReadout_norm_le (q : EuclideanSpace ℝ κ) (v : ι → ℝ)
    (vmax : ℝ) (hvmax : 0 ≤ vmax) (hv : ∀ i, |v i| ≤ vmax) :
    ‖blockReadout q v‖ ≤ vmax * ‖q‖ := by
  calc
    _ ≤ ‖blockDiagonal v‖ * ‖(blockInjection q).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖blockDiagonal v‖ * ‖(blockInjection q :
        EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι × κ))‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ vmax * ‖q‖ := mul_le_mul (blockDiagonal_norm_le v vmax hvmax hv)
      (blockInjection_norm_le q) (norm_nonneg _) hvmax

@[simp] theorem blockReadout_sub (qhat q : EuclideanSpace ℝ κ) (v : ι → ℝ) :
    blockReadout qhat v - blockReadout q v = blockReadout (qhat - q) v := by
  ext y i
  simp only [sub_apply, blockReadout_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib,
    mul_sub]

/-- One calibrated mode error bounds the full readout error uniformly in
the number of disjoint blocks. -/
theorem blockReadout_calibration (qhat q : EuclideanSpace ℝ κ) (v : ι → ℝ)
    (vmax : ℝ) (hvmax : 0 ≤ vmax) (hv : ∀ i, |v i| ≤ vmax) :
    ‖blockReadout qhat v - blockReadout q v‖ ≤ vmax * ‖qhat - q‖ := by
  rw [blockReadout_sub]
  exact blockReadout_norm_le _ v vmax hvmax hv

end Maxwell.Composition
