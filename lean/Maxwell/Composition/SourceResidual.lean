import Maxwell.Logical.SourceInverse
import Maxwell.Composition.DefectCoordinates

/-! Arbitrary-source residual transfer for the actual compiled square circuit.
The source is inserted at its input boundary equations, while every internal
equation error remains part of the complete Euclidean residual. -/

noncomputable section

namespace Maxwell.Composition.SourceResidual

open Maxwell.Logical

def sourceBoundary (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (Fin S.n) →L[ℝ]
      EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) :=
  coordinateExtension (sourceCircuit S precision).circuit.inputIndex

@[simp] theorem sourceBoundary_input (S : Source.SparseSystem) (precision : ℕ)
    (g : EuclideanSpace ℝ (Fin S.n)) (i : Fin S.n) :
    sourceBoundary S precision g ((sourceCircuit S precision).circuit.inputIndex i) = g i := by
  exact congrArg (fun x : EuclideanSpace ℝ (Fin S.n) => x i)
    (coordinateRestriction_extension _
      (sourceCircuit S precision).circuit.inputIndex_injective g)

theorem sourceBoundary_noninput (S : Source.SparseSystem) (precision : ℕ)
    (g : EuclideanSpace ℝ (Fin S.n))
    (j : Fin (sourceCircuit S precision).size) (hj : S.n ≤ j.val) :
    sourceBoundary S precision g j = 0 := by
  rw [sourceBoundary, coordinateExtension_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hne : (sourceCircuit S precision).circuit.inputIndex i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    rw [(sourceCircuit S precision).circuit.inputIndex_value] at hv
    have hi := i.isLt
    omega
  simp [hne]

theorem sourceBoundary_norm (S : Source.SparseSystem) (precision : ℕ)
    (g : EuclideanSpace ℝ (Fin S.n)) : ‖sourceBoundary S precision g‖ = ‖g‖ := by
  let pick := (sourceCircuit S precision).circuit.inputIndex
  have hinj := (sourceCircuit S precision).circuit.inputIndex_injective
  apply le_antisymm
  · calc
      _ ≤ ‖coordinateExtension pick‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right
        (coordinateExtension_norm_le pick hinj) (norm_nonneg _)
      _ = _ := one_mul _
  · calc
      ‖g‖ = ‖coordinateRestriction pick (sourceBoundary S precision g)‖ := by
        rw [sourceBoundary, coordinateRestriction_extension pick hinj]
      _ ≤ ‖coordinateRestriction pick‖ * ‖sourceBoundary S precision g‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖sourceBoundary S precision g‖ := mul_le_mul_of_nonneg_right
        (coordinateRestriction_norm_le pick hinj) (norm_nonneg _)
      _ = _ := one_mul _

theorem gate_residual_bound (S : Source.SparseSystem) (precision : ℕ)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size))
    (g : EuclideanSpace ℝ (Fin S.n)) (j : Fin (sourceCircuit S precision).size) :
    |(sourceCircuit S precision).circuit.residual
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
      (WithLp.ofLp state) j| ≤
      ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖ := by
  let c := (sourceCircuit S precision).circuit
  by_cases hj : j.val < S.n
  · let i : Fin S.n := ⟨j.val, hj⟩
    have he : c.inputIndex i = j := Fin.ext (c.inputIndex_value i)
    rw [← he, c.residual_at_input]
    simp [c, Circuit.originalInput]
  · rw [c.residual_noninput _ _ _ (Nat.le_of_not_gt hj)]
    have h := PiLp.norm_apply_le
      (sourceSquareOperator S precision state - sourceBoundary S precision g) j
    change |sourceSquareMap S precision (WithLp.ofLp state) j -
      sourceBoundary S precision g j| ≤ _ at h
    rw [sourceBoundary_noninput S precision g j (Nat.le_of_not_gt hj), sub_zero] at h
    simpa only [sourceSquareMap,
      Circuit.squareMap_noninput _ _ _ _ (Nat.le_of_not_gt hj)] using h

theorem output_residual_bound (S : Source.SparseSystem) (precision : ℕ)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size))
    (g : EuclideanSpace ℝ (Fin S.n)) (i : Fin S.n) :
    |state (sourceOutput S precision i) - g i| ≤
      ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖ := by
  have h := PiLp.norm_apply_le
    (sourceSquareOperator S precision state - sourceBoundary S precision g)
    ((sourceCircuit S precision).circuit.inputIndex i)
  change |sourceSquareMap S precision (WithLp.ofLp state)
    ((sourceCircuit S precision).circuit.inputIndex i) -
    sourceBoundary S precision g ((sourceCircuit S precision).circuit.inputIndex i)| ≤ _ at h
  simpa only [sourceBoundary_input, sourceSquareMap, Circuit.squareMap_input] using h

theorem rounded_residual_coordinate_le (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hp : 1 ≤ precision)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size))
    (g : EuclideanSpace ℝ (Fin S.n)) (i : Fin S.n) :
    |roundedProduct S precision
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i - g i| ≤
      ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖ := by
  have h := sourceCircuit_arbitrary_residual S hm precision hp
    ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))
    (WithLp.ofLp state)
    ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖
    (norm_nonneg _) (gate_residual_bound S precision state g)
  have hi : i.val < (sourceCircuit S precision).outputs.length := by
    rw [sourceCircuit_output_count]
    exact i.isLt
  have hv := h.get hi (by simp)
  simp only [List.get_ofFn] at hv
  change |state (sourceOutput S precision i) - roundedProduct S precision
    ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i| ≤ _ at hv
  calc
    _ ≤ |state (sourceOutput S precision i) - roundedProduct S precision
        ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i| +
        |state (sourceOutput S precision i) - g i| := by
      let a := state (sourceOutput S precision i)
      let b := roundedProduct S precision
        ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state)) i
      change |b - g i| ≤ |a - b| + |a - g i|
      calc
        _ = |(b - a) + (a - g i)| := by congr 1; ring
        _ ≤ |b - a| + |a - g i| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm b a]
    _ ≤ _ := by nlinarith [output_residual_bound S precision state g i]

/-- Every proposed state, with unrestricted auxiliary residuals, yields an
approximate solution of the actual rounded source system at its original inputs. -/
theorem rounded_residual_norm_le (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hp : 1 ≤ precision)
    (state : EuclideanSpace ℝ (Fin (sourceCircuit S precision).size))
    (g : EuclideanSpace ℝ (Fin S.n)) :
    ‖WithLp.toLp 2 (roundedProduct S precision
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))) - g‖ ≤
      Real.sqrt (S.n : ℝ) * ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖ := by
  have h := Target.WeightedDecoder.euclidean_norm_le_sqrt_card
    (WithLp.toLp 2 (roundedProduct S precision
      ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp state))) - g)
    (((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
      ‖sourceSquareOperator S precision state - sourceBoundary S precision g‖)
    (by positivity) (rounded_residual_coordinate_le S hm precision hp state g)
  simpa only [Fintype.card_fin, mul_assoc] using h

end Maxwell.Composition.SourceResidual
