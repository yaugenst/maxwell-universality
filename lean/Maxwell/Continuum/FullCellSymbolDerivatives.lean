import Maxwell.Continuum.FullCellCauchyGeometry

/-! All-order operator-norm Cauchy estimates for the literal full cell
resolvent, including the h-dependent distance to its selected pole. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary PeriodicBand OperatorFourier Set Metric

local instance fullCellDerivativeRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] fullCellSymbol

theorem realFullCellSymbol_contDiffAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Space} (hq : ‖realMomentumMap q‖ ≤ 4 * smallRadius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol (fullCellSymbol z σ)) q := by
  have hb : hessianEnergy (0 : Corner.Vec) ≤ (99 / 100 : ℝ)^2 * h^2 := by
    simp only [hessianEnergy_diagonal, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]
    positivity
  have ha := fullCellSymbol_tube_analyticAt D hh hσ0 hσ (fun j => q j) 0 hq hb
  have he : shiftedMomentum (fun j => q j) 0 = realMomentumMap q := by
    funext j
    change (q j : ℂ) + Complex.I * ((0 : ℝ) : ℂ) = (q j : ℂ)
    simp
  rw [he] at ha
  exact (ha.contDiffAt.restrict_scalars ℝ).comp q realMomentumMap.contDiff.contDiffAt

theorem fullCell_line_derivative_bound {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => fullCellSymbol z σ
      (realMomentumMap q + (s : ℂ) • realMomentumMap v)) 0‖ ≤
      ((2 : ℝ)^14 * (h^2)⁻¹) * ((2 : ℝ)^256 / h)^K * (K.factorial : ℝ)^2 := by
  have hpos := D.h_pos
  let f : ℂ → CellMap := fun s => fullCellSymbol z σ
    (realMomentumMap q + s • realMomentumMap v)
  have ha : AnalyticOnNhd ℂ f (closedBall 0 (fullCellRadius h)) :=
    fullCell_line_analytic D hh hσ0 hσ hq hv
  have hc : ∀ s ∈ closedBall (0 : ℂ) (fullCellRadius h),
      ‖f s‖ ≤ (2 : ℝ)^14 * (h^2)⁻¹ := by
    intro s hs
    exact fullCell_line_norm_le D hh hσ0 hσ hq hv hs
  change ‖iteratedDeriv K (fun s : ℝ => f s) 0‖ ≤ _
  rw [OperatorFourier.iteratedDeriv_restrict_complex f (ball 0 (fullCellRadius h))
    isOpen_ball (ha.mono ball_subset_closedBall) K 0
    (by simpa using fullCellRadius_pos D.h_pos)]
  have hd := CauchyBounds.norm_iteratedDeriv_le K ha hc
    (fullCellRadius_pos D.h_pos) (c := 0) (by simp)
  have hfac : (K.factorial : ℝ) ≤ (K.factorial : ℝ)^2 := by
    have hp : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_pos K
    nlinarith
  calc
    _ ≤ K.factorial * ((2 : ℝ)^14 * (h^2)⁻¹) / (fullCellRadius h)^K := hd
    _ = ((2 : ℝ)^14 * (h^2)⁻¹) * ((2 : ℝ)^256 / h)^K * K.factorial := by
      have hr : (fullCellRadius h)⁻¹ = (2 : ℝ)^256 / h := by
        rw [fullCellRadius, inv_div]
      have hrK : ((fullCellRadius h)^K)⁻¹ = ((2 : ℝ)^256 / h)^K := by
        rw [← inv_pow]
        exact congrArg (fun r : ℝ => r^K) hr
      rw [div_eq_mul_inv, hrK]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)

theorem realFullCellSymbol_line_bound {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => realSymbol (fullCellSymbol z σ) (q + s • v)) 0‖ ≤
      ((2 : ℝ)^14 * (h^2)⁻¹) * ((2 : ℝ)^256 / h)^K * (K.factorial : ℝ)^2 := by
  have he : (fun s : ℝ => realSymbol (fullCellSymbol z σ) (q + s • v)) =
      (fun s : ℝ => fullCellSymbol z σ
        (realMomentumMap q + (s : ℂ) • realMomentumMap v)) := by
    funext s
    rw [realSymbol, map_add, map_smul]
    rfl
  rw [he]
  exact fullCell_line_derivative_bound D hh hσ0 hσ hq hv K

#print axioms realFullCellSymbol_contDiffAt
#print axioms realFullCellSymbol_line_bound

end Maxwell.Continuum.CellGauge
