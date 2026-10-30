import Maxwell.Continuum.PeriodicGlobalDenominator
import Maxwell.Continuum.MasterConstantLedger

/-! The actual other-band inverse after rescaling has an h² factor in
every fixed-order derivative. This is an operator-norm statement on the
full cell Hilbert space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary CellGauge Set Metric

attribute [local irreducible] separatedCellSymbol poleMomentum imaginaryPole

def scaledSeparatedCell {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) : CellMap :=
  ((h^2 : ℝ) : ℂ) • separatedCellSymbol z 0 (poleMomentum D hh j k)

theorem globalPole_unit_line_chart {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1/16) :
    ‖poleMomentum D hh j (realMomentum k.ofLp + ζ • v)‖ ≤ separatedRadius :=
  globalPole_momentum_chart D hh j k hk hv (hζ.trans (by
    have hr := globalPoleRadius_ge_one k
    linarith only [hr]))

theorem scaledSeparatedCell_line_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => scaledSeparatedCell D hh j (realMomentum k.ofLp + ζ • v))
      (closedBall 0 (1/16)) := by
  intro ζ hζ
  have hp := globalPole_unit_line_chart D hh j k hk hv
    (by simpa only [mem_closedBall, dist_zero_right] using hζ)
  have ha : AnalyticAt ℂ (fun w : ℂ => poleMomentum D hh j (realMomentum k.ofLp + w • v)) ζ := by
    unfold poleMomentum
    exact analyticAt_const.add ((analyticAt_const.add
      (analyticAt_id.smul analyticAt_const)).const_smul (c := (h : ℂ)))
  have he := AnalyticAt.comp (f := fun w : ℂ => poleMomentum D hh j (realMomentum k.ofLp + w • v))
    (separatedCellSymbol_analytic D le_rfl (by positivity) _
      (by simpa only [mem_closedBall, dist_zero_right] using hp)) ha
  unfold scaledSeparatedCell
  convert! he.const_smul (c := ((h^2 : ℝ) : ℂ)) using 1

theorem scaledSeparatedCell_line_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1/16) :
    ‖scaledSeparatedCell D hh j (realMomentum k.ofLp + ζ • v)‖ ≤ (2 : ℝ)^116*h^2 := by
  rw [scaledSeparatedCell, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg h)]
  exact (mul_le_mul_of_nonneg_left (separatedCellSymbol_norm_le D le_rfl (by positivity)
    (globalPole_unit_line_chart D hh j k hk hv hζ)) (sq_nonneg h)).trans_eq (mul_comm _ _)

theorem scaledSeparatedCell_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun ζ : ℂ =>
      scaledSeparatedCell D hh j (realMomentum k.ofLp + ζ • v)) 0‖ ≤ (2 : ℝ)^352*h^2 := by
  have he := CauchyBounds.norm_iteratedDeriv_le n
    (scaledSeparatedCell_line_analytic D hh j k hk hv)
    (fun ζ hζ => scaledSeparatedCell_line_norm D hh j k hk hv
      (by simpa only [mem_closedBall, dist_zero_right] using hζ))
    (r := (1/16 : ℝ)) (c := (0 : ℂ)) (by norm_num) (by simp)
  have hf : (n.factorial : ℝ) ≤ (2 : ℝ)^160 :=
    (show (n.factorial : ℝ) ≤ (Nat.factorial 32 : ℕ) by
      exact_mod_cast Nat.factorial_le (show n ≤ 32 by omega)).trans MasterConstants.factorial32_le_power
  have hp : (16 : ℝ)^n ≤ (2 : ℝ)^64 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  apply he.trans
  rw [div_pow, one_pow, div_div_eq_mul_div, div_one]
  calc
    _ ≤ (2 : ℝ)^160*((2 : ℝ)^116*h^2)*(2 : ℝ)^64 := by gcongr
    _ = (2 : ℝ)^340*h^2 := by rw [show 340 = 160+116+64 by omega, pow_add, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (sq_nonneg h)

end Maxwell.Continuum.PeriodicBand
