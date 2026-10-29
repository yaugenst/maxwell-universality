import Maxwell.Composition.PhysicalReadout

/-! Source and field amplitudes from actual scalar-defect coordinate maps.
The source estimate uses the unit local mode, injective coordinate extension,
and the proved inverse square-root weight bound, with no source-norm premise. -/

noncomputable section

namespace Maxwell.Composition

variable {B : Target.Box} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {blocks : ι → Finset B.Cell}

theorem DefectLayout.localIdealSource_norm_le (layout : DefectLayout (κ := κ) blocks)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (J : ℝ) (hJ : 0 ≤ J)
    (hK : ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ J)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℝ ι) :
    ‖localIdealSource K layout.weightEquiv (coordinateExtension layout.pick)
      (blockInjection u g)‖ ≤ 2 * J * ‖g‖ := by
  classical
  have hQ (x : EuclideanSpace ℝ (ι × κ)) : ‖coordinateExtension layout.pick x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖coordinateExtension layout.pick‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (coordinateExtension_norm_le layout.pick layout.injective) (norm_nonneg _)
      _ = _ := one_mul _
  have hW (x : EuclideanSpace ℝ (ι × κ)) : ‖layout.weightEquiv.symm x‖ ≤ 2 * ‖x‖ := by
    calc
      _ ≤ ‖(layout.weightEquiv.symm : EuclideanSpace ℝ (ι × κ) →L[ℝ]
          EuclideanSpace ℝ (ι × κ))‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right layout.weightEquiv_inverse_norm_le (norm_nonneg _)
  calc
    _ ≤ ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ *
        ‖coordinateExtension layout.pick (layout.weightEquiv.symm (blockInjection u g))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ J * (2 * ‖blockInjection u g‖) := mul_le_mul hK
      ((hQ _).trans (hW _)) (norm_nonneg _) hJ
    _ = _ := by rw [blockInjection_norm_apply, hu]; ring

theorem DefectLayout.scaled_idealSource_norm_le (layout : DefectLayout (κ := κ) blocks)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (α J : ℝ) (hα : 0 ≤ α) (hJ : 0 ≤ J)
    (hK : ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ J)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℝ ι) :
    ‖α • localIdealSource K layout.weightEquiv (coordinateExtension layout.pick)
      (blockInjection u g)‖ ≤ 2 * α * J * ‖g‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  calc
    _ ≤ α * (2 * J * ‖g‖) := mul_le_mul_of_nonneg_left
      (layout.localIdealSource_norm_le K J hJ hK u hu g) hα
    _ = _ := by ring

/-- The calibration routine's exact shared-mode source obeys the same bound
as the local physical source identity. -/
theorem DefectLayout.shared_modeSource_norm_le (layout : DefectLayout (κ := κ) blocks)
    (w : κ → ℚ) (hweight : ∀ i j, layout.weight (i, j) = w j)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (α J : ℝ) (hα : 0 ≤ α) (hJ : 0 ≤ J)
    (hK : ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ J)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℝ ι) :
    ‖modeSource α (K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)
      (coordinateExtension layout.pick) layout.inverseWeight (weightedLocalMode w u) g‖ ≤
      2 * α * J * ‖g‖ := by
  rw [layout.shared_source w hweight u g α K]
  have h := layout.localIdealSource_norm_le K J hJ hK u hu (α • g)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα] at h
  convert h using 1
  ring

/-- Actual source calibration and final rounding preserve a uniform emitted
source bound; the ideal-source amplitude is proved from the layout above. -/
theorem DefectLayout.emitted_source_norm_le (layout : DefectLayout (κ := κ) blocks)
    (K : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (α J L ε : ℝ) (hα : 0 ≤ α) (hJ : 1 ≤ J) (hL : 1 ≤ L) (hε : ε ≤ 1)
    (hK : ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ J)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℝ ι)
    (f : EuclideanSpace ℝ B.Edge)
    (herror : ‖f - α • localIdealSource K layout.weightEquiv (coordinateExtension layout.pick)
      (blockInjection u g)‖ ≤ α * ε * ‖g‖ / (8192 * L)) :
    ‖f‖ ≤ 4 * α * J * ‖g‖ := by
  have hJ0 : 0 ≤ J := le_trans zero_le_one hJ
  have hideal := layout.scaled_idealSource_norm_le K α J hα hJ0 hK u hu g
  have hbudget : α * ε * ‖g‖ / (8192 * L) ≤ α * J * ‖g‖ := by
    calc
      _ ≤ α * ‖g‖ / (8192 * L) := div_le_div_of_nonneg_right
        (by nlinarith [mul_nonneg hα (norm_nonneg g)]) (by positivity)
      _ ≤ α * ‖g‖ := div_le_self (mul_nonneg hα (norm_nonneg _)) (by linarith)
      _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hα (norm_nonneg g)) (sub_nonneg.mpr hJ)]
  have htriangle := norm_le_norm_sub_add f
    (α • localIdealSource K layout.weightEquiv (coordinateExtension layout.pick) (blockInjection u g))
  nlinarith [mul_nonneg (mul_nonneg hα hJ0) (norm_nonneg g)]

/-- The full inverse estimate and any field with relative residual at most
one half give a field bound from the actual emitted-source construction. -/
theorem DefectLayout.emitted_field_norm_le (layout : DefectLayout (κ := κ) blocks)
    (K A : EuclideanSpace ℝ B.Edge ≃L[ℝ] EuclideanSpace ℝ B.Edge)
    (α J L ε Q : ℝ) (hα : 0 ≤ α) (hJ : 1 ≤ J) (hL : 1 ≤ L) (hε : ε ≤ 1)
    (hK : ‖(K : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ J)
    (hA : ‖(A.symm : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ ≤ Q)
    (u : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℝ ι)
    (f y : EuclideanSpace ℝ B.Edge)
    (herror : ‖f - α • localIdealSource K layout.weightEquiv (coordinateExtension layout.pick)
      (blockInjection u g)‖ ≤ α * ε * ‖g‖ / (8192 * L))
    (hres : ‖A y - f‖ ≤ ‖f‖ / 2) :
    ‖y‖ ≤ 6 * α * J * Q * ‖g‖ := by
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hA
  have hf := layout.emitted_source_norm_le K α J L ε hα hJ hL hε hK u hu g f herror
  have hy : ‖y‖ ≤ Q * (‖A y - f‖ + ‖f‖) := by
    calc
      ‖y‖ = ‖A.symm (A y)‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖(A.symm : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge)‖ * ‖A y‖ :=
        ContinuousLinearMap.le_opNorm
          (A.symm : EuclideanSpace ℝ B.Edge →L[ℝ] EuclideanSpace ℝ B.Edge) (A y)
      _ ≤ Q * (‖A y - f‖ + ‖f‖) :=
        mul_le_mul hA (norm_le_norm_sub_add _ _) (norm_nonneg _) hQ
  calc
    _ ≤ Q * (‖f‖ / 2 + ‖f‖) := hy.trans
      (mul_le_mul_of_nonneg_left (add_le_add hres le_rfl) hQ)
    _ = (3 / 2 : ℝ) * Q * ‖f‖ := by ring
    _ ≤ (3 / 2 : ℝ) * Q * (4 * α * J * ‖g‖) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

end Maxwell.Composition
