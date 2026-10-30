import Maxwell.Continuum.CellSourceTranslation
import Maxwell.Continuum.SourceNumeratorDerivatives

/-! The actual compact source assembled from its finitely many physical
cells, with a holomorphic Bloch phase at complex momentum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory EffectiveMass Bloch Set

def cellSourcePacket (h : ℝ) (u : FieldL2) (q : Momentum) : CellFieldL2 :=
  ∑ a ∈ ballCells h⁻¹, sourceLatticeFactor (-q) a • restrictLatticeCell a (sourceMode h u)

theorem sourceLatticeFactor_analytic (a : Bloch.Alias) (q : Momentum) :
    AnalyticAt ℂ (fun p => sourceLatticeFactor p a) q := by
  apply AnalyticAt.mul _ analyticAt_const
  apply AnalyticAt.cexp
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_sum _ (fun j _ =>
    ((ContinuousLinearMap.proj j : Momentum →L[ℂ] ℂ).analyticAt q).mul analyticAt_const)

theorem cellSourcePacket_analytic (h : ℝ) (u : FieldL2) (q : Momentum) :
    AnalyticAt ℂ (cellSourcePacket h u) q := by
  apply Finset.analyticAt_fun_sum
  intro a _
  exact ((sourceLatticeFactor_analytic a (-q)).comp (f := fun p : Momentum => -p)
    analyticAt_id.neg).smul analyticAt_const

theorem restrictLatticeCell_norm_le_projection (a : Bloch.Alias) (f : FieldL2) :
    ‖restrictLatticeCell a f‖ ≤ ‖cellProjection a f‖ := by
  have he := embedLatticeCell_norm_sq a (restrictLatticeCell a f)
  change ‖cellProjection a f‖^2 = 8*‖restrictLatticeCell a f‖^2 at he
  nlinarith only [he, norm_nonneg (restrictLatticeCell a f), norm_nonneg (cellProjection a f),
    sq_nonneg ‖restrictLatticeCell a f‖]

theorem sourceLatticeFactor_norm (q : Momentum) (a : Bloch.Alias) :
    ‖sourceLatticeFactor q a‖ = ‖spatialPhase q (latticeShift a)‖ := by
  rw [sourceLatticeFactor, norm_mul, carrier_norm, mul_one]

theorem sourceLatticeFactor_norm_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (q : Momentum) {a : Bloch.Alias} (ha : a ∈ ballCells h⁻¹) :
    ‖sourceLatticeFactor (-q) a‖ ≤ Real.exp (24*h⁻¹*‖sourceImaginary q‖) := by
  rw [sourceLatticeFactor_norm]
  apply (sourcePhase_norm_le (-q) (latticeShift a)).trans
  apply Real.exp_le_exp.mpr
  rw [sourceImaginary_neg, norm_neg]
  have hL : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hn := ballCells_shift_norm_le hL ha
  nlinarith only [mul_le_mul_of_nonneg_left hn (norm_nonneg (sourceImaginary q))]

theorem cellSourcePacket_norm_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (u : FieldL2) (q : Momentum) :
    ‖cellSourcePacket h u q‖ ≤ Real.exp (24*h⁻¹*‖sourceImaginary q‖) *
      Real.sqrt ((ballCells h⁻¹).card : ℝ) * ‖u‖ := by
  let C := Real.exp (24*h⁻¹*‖sourceImaginary q‖)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  calc
    _ ≤ ∑ a ∈ ballCells h⁻¹, ‖sourceLatticeFactor (-q) a • restrictLatticeCell a (sourceMode h u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ ballCells h⁻¹, C*‖cellProjection a (sourceMode h u)‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_smul]
      exact mul_le_mul (sourceLatticeFactor_norm_le hh hh1 q ha)
        (restrictLatticeCell_norm_le_projection a _) (norm_nonneg _) hC
    _ = C * ∑ a ∈ ballCells h⁻¹, ‖cellProjection a (sourceMode h u)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.sqrt ((ballCells h⁻¹).card : ℝ) * ‖sourceMode h u‖) :=
      mul_le_mul_of_nonneg_left (familyProjection_sum_norm_le _ _) hC
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sourceMode_norm_le h u) (Real.sqrt_nonneg _)) hC

#print axioms cellSourcePacket_norm_le

end Maxwell.Continuum.CellGauge
