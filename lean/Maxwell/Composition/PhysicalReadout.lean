import Maxwell.Composition.Weights
import Maxwell.Composition.Calibration

/-! The physical weighted readout is exactly the finite local dot product.
This binds the mode-calibration estimates to the scalar-cell coordinate
assembly, including the square-root weights. -/

noncomputable section

namespace Maxwell.Composition

open scoped BigOperators

theorem inv_sqrt_mul_self (w : ℝ) (hw : 0 < w) :
    (Real.sqrt w)⁻¹ * w = Real.sqrt w := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  calc
    (Real.sqrt w)⁻¹ * w = (Real.sqrt w)⁻¹ * (Real.sqrt w * Real.sqrt w) := by
      rw [← pow_two, Real.sq_sqrt hw.le]
    _ = Real.sqrt w := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem inv_mul_sqrt (w : ℝ) (hw : 0 < w) :
    w⁻¹ * Real.sqrt w = (Real.sqrt w)⁻¹ := by
  calc
    w⁻¹ * Real.sqrt w = w⁻¹ * ((Real.sqrt w)⁻¹ * w) := by
      rw [inv_sqrt_mul_self w hw]
    _ = (Real.sqrt w)⁻¹ := by rw [mul_left_comm, inv_mul_cancel₀ hw.ne', mul_one]

theorem blockInjection_adjoint_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ κ) (d : EuclideanSpace ℝ (ι × κ)) (i : ι) :
    (blockInjection u).adjoint d i = ∑ j, u j * d (i, j) := by
  simpa [blockReadout] using blockReadout_apply u (fun _ : ι => 1) d i

section ActualCoordinates

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {blocks : ι → Finset B.Cell}

theorem DefectLayout.weightedCoordinates_apply (layout : DefectLayout (κ := κ) blocks)
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) (y : EuclideanSpace ℝ B.Edge) (ij : ι × κ) :
    weightedDefectCoordinates (layout.strengthEquiv v hv) layout.weightEquiv
      (coordinateRestriction layout.pick) y ij =
      (v ij.1 : ℝ) * layout.sqrtWeight ij * y (layout.pick ij) := by
  change (layout.sqrtWeight ij)⁻¹ *
    (((v ij.1 * layout.weight ij : ℚ) : ℝ) * y (layout.pick ij)) = _
  rw [Rat.cast_mul]
  have hw : 0 < (layout.weight ij : ℝ) := by
    apply Rat.cast_pos.mpr
    exact lt_of_lt_of_le (by norm_num) (layout.weight_bounds ij).1
  have hs : (layout.sqrtWeight ij)⁻¹ * (layout.weight ij : ℝ) =
      layout.sqrtWeight ij := inv_sqrt_mul_self _ hw
  calc
    _ = (v ij.1 : ℝ) * ((layout.sqrtWeight ij)⁻¹ * (layout.weight ij : ℝ)) *
        y (layout.pick ij) := by ring
    _ = _ := by rw [hs]

/-- The exact physical bright coordinates query only the actual finite
defect coordinates. This formula precedes every calibration estimate. -/
theorem DefectLayout.readout_action (layout : DefectLayout (κ := κ) blocks)
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) (u : EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ B.Edge) (i : ι) :
    (blockInjection u).adjoint
      (weightedDefectCoordinates (layout.strengthEquiv v hv) layout.weightEquiv
        (coordinateRestriction layout.pick) y) i =
      (v i : ℝ) * ∑ j, layout.sqrtWeight (i, j) * u j * y (layout.pick (i, j)) := by
  rw [blockInjection_adjoint_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [layout.weightedCoordinates_apply]
  ring

def weightedLocalMode (w : κ → ℚ) (u : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 fun j => Real.sqrt (w j : ℝ) * u j

/-- When the physical layout is a collection of translated copies of one
local weight stencil, the actual readout is exactly the shared-mode map
used by the calibrated decoder. Translation/stencil equality is an explicit
layout property, separate from every spectral conclusion. -/
theorem DefectLayout.shared_readout (layout : DefectLayout (κ := κ) blocks)
    (w : κ → ℚ) (hweight : ∀ i j, layout.weight (i, j) = w j)
    (v : ι → ℚ) (hv : ∀ i, v i ≠ 0) (u : EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ B.Edge) :
    (blockInjection u).adjoint
      (weightedDefectCoordinates (layout.strengthEquiv v hv) layout.weightEquiv
        (coordinateRestriction layout.pick) y) =
      blockReadout (weightedLocalMode w u) (fun i => (v i : ℝ))
        (coordinateRestriction layout.pick y) := by
  ext i
  rw [layout.readout_action, blockReadout_apply]
  simp [DefectLayout.sqrtWeight, hweight, weightedLocalMode]

def DefectLayout.inverseWeight (layout : DefectLayout (κ := κ) blocks) :
    EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  blockDiagonal (fun ij => (layout.weight ij : ℝ)⁻¹)

theorem DefectLayout.inverseWeight_norm_le (layout : DefectLayout (κ := κ) blocks) :
    ‖layout.inverseWeight‖ ≤ 4 := by
  apply blockDiagonal_norm_le (fun ij => (layout.weight ij : ℝ)⁻¹) 4 (by norm_num)
  intro ij
  have hw : (1 / 4 : ℝ) ≤ (layout.weight ij : ℝ) := by
    have h : (((1 / 4 : ℚ) : ℝ)) ≤ (layout.weight ij : ℝ) :=
      Rat.cast_le.mpr (layout.weight_bounds ij).1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  rw [abs_inv, abs_of_nonneg (le_trans (by norm_num) hw)]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hw
  norm_num only [one_div, inv_inv] at h
  exact h

theorem DefectLayout.shared_source_injection (layout : DefectLayout (κ := κ) blocks)
    (w : κ → ℚ) (hweight : ∀ i j, layout.weight (i, j) = w j)
    (u : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    layout.inverseWeight (blockInjection (weightedLocalMode w u) g) =
      layout.weightEquiv.symm (blockInjection u g) := by
  ext ij
  rcases ij with ⟨i, j⟩
  change (layout.weight (i, j) : ℝ)⁻¹ *
    ((Real.sqrt (w j : ℝ) * u j) * g i) =
      (layout.sqrtWeight (i, j))⁻¹ * (u j * g i)
  have hw : 0 < (w j : ℝ) := by
    rw [← hweight i j]
    apply Rat.cast_pos.mpr
    exact lt_of_lt_of_le (by norm_num) (layout.weight_bounds (i, j)).1
  rw [DefectLayout.sqrtWeight, hweight i j]
  calc
    _ = ((w j : ℝ)⁻¹ * Real.sqrt (w j : ℝ)) * (u j * g i) := by ring
    _ = _ := by rw [inv_mul_sqrt _ hw]

/-- The exact local source in the physical residual identity is the
unrounded source evaluated by the shared q=W^(1/2)u calibration routine.
The implementation uses W^(-1)q, so its norm budget is four rather than
the inverse square-root budget two. -/
theorem DefectLayout.shared_source (layout : DefectLayout (κ := κ) blocks)
    (w : κ → ℚ) (hweight : ∀ i j, layout.weight (i, j) = w j)
    (u : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι)
    (α : ℝ) (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge) :
    modeSource α (K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)
      (coordinateExtension layout.pick) layout.inverseWeight (weightedLocalMode w u) g =
      localIdealSource K layout.weightEquiv (coordinateExtension layout.pick)
        (blockInjection u (α • g)) := by
  rw [modeSource, layout.shared_source_injection w hweight u g]
  simp [localIdealSource]

end ActualCoordinates

end Maxwell.Composition
