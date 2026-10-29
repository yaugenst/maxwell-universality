import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-! Actual Euclidean sum-coordinate decomposition. These maps do not use
the maximum norm on an ordinary product of normed spaces. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def sumLeftInjection : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Sum.elim x (fun _ => 0))
      map_add' := by intro x y; ext i; cases i <;> simp
      map_smul' := by intro a x; ext i; cases i <;> simp }

def sumRightInjection : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Sum.elim (fun _ => 0) x)
      map_add' := by intro x y; ext i; cases i <;> simp
      map_smul' := by intro a x; ext i; cases i <;> simp }

def sumLeftProjection : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Sum.inl i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def sumRightProjection : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Sum.inr i))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem sumLeftInjection_inl (x : EuclideanSpace ℝ ι) (i : ι) :
    sumLeftInjection (κ := κ) x (Sum.inl i) = x i := rfl

@[simp] theorem sumLeftInjection_inr (x : EuclideanSpace ℝ ι) (j : κ) :
    sumLeftInjection x (Sum.inr j) = 0 := rfl

@[simp] theorem sumRightInjection_inl (x : EuclideanSpace ℝ κ) (i : ι) :
    sumRightInjection x (Sum.inl i) = 0 := rfl

@[simp] theorem sumRightInjection_inr (x : EuclideanSpace ℝ κ) (j : κ) :
    sumRightInjection (ι := ι) x (Sum.inr j) = x j := rfl

@[simp] theorem sumLeftProjection_apply (x : EuclideanSpace ℝ (ι ⊕ κ)) (i : ι) :
    sumLeftProjection x i = x (Sum.inl i) := rfl

@[simp] theorem sumRightProjection_apply (x : EuclideanSpace ℝ (ι ⊕ κ)) (j : κ) :
    sumRightProjection x j = x (Sum.inr j) := rfl

@[simp] theorem sumLeftProjection_left (x : EuclideanSpace ℝ ι) :
    sumLeftProjection (sumLeftInjection (κ := κ) x) = x := by ext i; rfl

@[simp] theorem sumRightProjection_right (x : EuclideanSpace ℝ κ) :
    sumRightProjection (sumRightInjection (ι := ι) x) = x := by ext i; rfl

@[simp] theorem sumLeftProjection_right (x : EuclideanSpace ℝ κ) :
    sumLeftProjection (sumRightInjection (ι := ι) x) = 0 := by ext i; rfl

@[simp] theorem sumRightProjection_left (x : EuclideanSpace ℝ ι) :
    sumRightProjection (sumLeftInjection (κ := κ) x) = 0 := by ext i; rfl

theorem sumCoordinate_decomposition (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    x = sumLeftInjection (sumLeftProjection x) +
      sumRightInjection (sumRightProjection x) := by
  ext i
  cases i <;> simp

theorem sumCoordinate_norm_sq (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖x‖ ^ 2 = ‖sumLeftProjection x‖ ^ 2 + ‖sumRightProjection x‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]

theorem sumLeftInjection_norm_apply (x : EuclideanSpace ℝ ι) :
    ‖sumLeftInjection (κ := κ) x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sumCoordinate_norm_sq]
  simp

theorem sumRightInjection_norm_apply (x : EuclideanSpace ℝ κ) :
    ‖sumRightInjection (ι := ι) x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sumCoordinate_norm_sq]
  simp

theorem sumLeftProjection_norm_apply_le (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖sumLeftProjection x‖ ≤ ‖x‖ := by
  have h := sumCoordinate_norm_sq x
  nlinarith only [h, sq_nonneg ‖sumRightProjection x‖,
    norm_nonneg x, norm_nonneg (sumLeftProjection x)]

theorem sumRightProjection_norm_apply_le (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖sumRightProjection x‖ ≤ ‖x‖ := by
  have h := sumCoordinate_norm_sq x
  nlinarith only [h, sq_nonneg ‖sumLeftProjection x‖,
    norm_nonneg x, norm_nonneg (sumRightProjection x)]

theorem sumLeftInjection_norm_le : ‖sumLeftInjection (ι := ι) (κ := κ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [sumLeftInjection_norm_apply]

theorem sumRightInjection_norm_le : ‖sumRightInjection (ι := ι) (κ := κ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [sumRightInjection_norm_apply]

theorem sumLeftProjection_norm_le : ‖sumLeftProjection (ι := ι) (κ := κ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using sumLeftProjection_norm_apply_le x

theorem sumRightProjection_norm_le : ‖sumRightProjection (ι := ι) (κ := κ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using sumRightProjection_norm_apply_le x

end Maxwell.Composition
