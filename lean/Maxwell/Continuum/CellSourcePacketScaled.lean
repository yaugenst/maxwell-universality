import Maxwell.Continuum.CellSourcePacket

/-! Uniform scaled norm of the actual finite-cell source packet.
The spatial cell count cancels its physical source normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier MeasureTheory EffectiveMass Bloch Set

theorem sourceScale_sqrt_cellCount {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    sourceScale h * Real.sqrt ((ballCells h⁻¹).card : ℝ) ≤ 32 := by
  have hL : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hb := ballCells_card_le hL
  have hs : (sourceScale h)^2 = h^3 := by
    rw [sourceScale, mul_pow, Real.sq_sqrt hh.le]
    ring
  have ht : (sourceScale h * Real.sqrt ((ballCells h⁻¹).card : ℝ))^2 ≤ (32 : ℝ)^2 := by
    rw [mul_pow, hs, Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ h^3*((2 : ℝ)^10*(h⁻¹)^3) := mul_le_mul_of_nonneg_left hb (pow_nonneg hh.le 3)
      _ = _ := by field_simp; ring
  exact (sq_le_sq₀ (mul_nonneg (sourceScale_pos hh).le (Real.sqrt_nonneg _)) (by norm_num)).mp ht

def scaledCellSourcePacket (h : ℝ) (u : FieldL2) (k : Momentum) : CellFieldL2 :=
  (sourceScale h : ℂ) • cellSourcePacket h u ((h : ℂ) • k)

theorem scaledCellSourcePacket_analytic (h : ℝ) (u : FieldL2) (k : Momentum) :
    AnalyticAt ℂ (scaledCellSourcePacket h u) k := by
  let S : CellFieldL2 →L[ℂ] CellFieldL2 := (sourceScale h : ℂ) • ContinuousLinearMap.id ℂ CellFieldL2
  let H : Momentum →L[ℂ] Momentum := (h : ℂ) • ContinuousLinearMap.id ℂ Momentum
  exact (S.analyticAt _).comp (f := fun p => cellSourcePacket h u (H p))
    ((cellSourcePacket_analytic h u (H k)).comp (f := H) (H.analyticAt k))

theorem scaledCellSourcePacket_norm_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : FieldL2) (k : Momentum) :
    ‖scaledCellSourcePacket h u k‖ ≤ 32*Real.exp (24*‖sourceImaginary k‖)*‖u‖ := by
  rw [scaledCellSourcePacket, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceScale_pos hh)]
  have he : 24*h⁻¹*‖sourceImaginary ((h : ℂ) • k)‖ = 24*‖sourceImaginary k‖ := by
    rw [sourceImaginary_real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  have hb := cellSourcePacket_norm_le hh hh1 u ((h : ℂ) • k)
  rw [he] at hb
  calc
    _ ≤ sourceScale h * (Real.exp (24*‖sourceImaginary k‖)*Real.sqrt ((ballCells h⁻¹).card : ℝ)*‖u‖) :=
      mul_le_mul_of_nonneg_left hb (sourceScale_pos hh).le
    _ = (sourceScale h*Real.sqrt ((ballCells h⁻¹).card : ℝ))*Real.exp (24*‖sourceImaginary k‖)*‖u‖ := by ring
    _ ≤ _ := by
      gcongr
      exact sourceScale_sqrt_cellCount hh hh1

#print axioms scaledCellSourcePacket_norm_le

end Maxwell.Continuum.CellGauge
