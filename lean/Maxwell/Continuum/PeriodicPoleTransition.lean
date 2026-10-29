import Maxwell.Continuum.PeriodicTubeTransition
import Maxwell.Continuum.PeriodicPoleScaled

/-! The fixed transition-shell inverse bound remains valid all the way
to the constructed imaginary pole in each coordinate direction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] imaginaryPole CellGauge.fullCellSymbol

theorem hessianEnergy_single (j : Fin 3) (x : ℝ) :
    hessianEnergy (Pi.single j x) = hessian j j * x^2 := by
  simp [hessianEnergy_diagonal, Pi.single_apply]

theorem imaginaryPole_hessianEnergy {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    hessianEnergy (Pi.single j (imaginaryPole D hh j)) ≤ 4 * h^2 := by
  calc
    _ = hessian j j * (imaginaryPole D hh j)^2 := hessianEnergy_single j _
    _ ≤ hessian j j * (poleUpper h j)^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (imaginaryPole_pos D hh j).le (imaginaryPole_bounds D hh j).2 2)
        (hessian_diagonal_positive j).le
    _ = (101 / 100 : ℝ)^2 * h^2 := pole_endpoint_square h (101 / 100) j
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg h)

theorem hessianEnergy_segment_le (b : Corner.Vec) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : hessianEnergy (s • b) ≤ hessianEnergy b := by
  rw [hessianEnergy_smul]
  have hs2 : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs2 (hessianEnergy_nonneg b)

theorem imaginaryPole_transition_cell_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q : Corner.Vec)
    (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖CellGauge.fullCellSymbol z σ
      (shiftedMomentum q (s • Pi.single j (imaginaryPole D hh j)))‖ ≤ (2 : ℝ)^196 :=
  transition_cell_norm_le D hh hσ0 hσ q _ hq0 hq
    ((hessianEnergy_segment_le _ hs).trans (imaginaryPole_hessianEnergy D hh j))

theorem imaginaryPole_transition_cell_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q : Corner.Vec)
    (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    AnalyticAt ℂ (CellGauge.fullCellSymbol z σ)
      (shiftedMomentum q (s • Pi.single j (imaginaryPole D hh j))) :=
  transition_cell_analyticAt D hh hσ0 hσ q _ hq0 hq
    ((hessianEnergy_segment_le _ hs).trans (imaginaryPole_hessianEnergy D hh j))

end Maxwell.Continuum.PeriodicBand
