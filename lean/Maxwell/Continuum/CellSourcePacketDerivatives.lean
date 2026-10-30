import Maxwell.Continuum.CellSourcePacketScaled
import Maxwell.Continuum.CauchyBounds

/-! Uniform complex directional derivatives of the actual normalized source
packet. The bound is independent of the number of occupied physical cells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier EffectiveMass Set Metric

theorem scaledCellSourcePacket_norm_ledger {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u : FieldL2} (hu : ‖u‖ ≤ 1) {k : Momentum} (hi : ‖sourceImaginary k‖ ≤ 10) :
    ‖scaledCellSourcePacket h u k‖ ≤ (2 : ℝ)^512 := by
  have he : Real.exp (240 : ℝ) ≤ (3 : ℝ)^240 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 240
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  apply (scaledCellSourcePacket_norm_le hh hh1 u k).trans
  calc
    _ ≤ 32*(3 : ℝ)^240*1 := by
      apply mul_le_mul _ hu (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Real.exp_le_exp.mpr (by linarith only [hi])).trans he
    _ ≤ _ := by norm_num

theorem scaledCellSourcePacket_iteratedDeriv_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u : FieldL2} (hu : ‖u‖ ≤ 1) {k v : Momentum}
    (hi : ‖sourceImaginary k‖ ≤ 8) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun z : ℂ => scaledCellSourcePacket h u (k + z • v)) 0‖ ≤
      n.factorial * (2 : ℝ)^512 := by
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => scaledCellSourcePacket h u (k + z • v))
      (closedBall 0 1) := by
    intro z _
    exact (scaledCellSourcePacket_analytic h u (k + z • v)).comp
      (f := fun z : ℂ => k + z • v) (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hb : ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖scaledCellSourcePacket h u (k + z • v)‖ ≤ (2 : ℝ)^512 := by
    intro z hz
    apply scaledCellSourcePacket_norm_ledger hh hh1 hu
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [sourceImaginary_add]
    apply (norm_add_le _ _).trans
    have hd := sourceImaginary_norm_le (z • v)
    rw [norm_smul] at hd
    have hp : ‖z‖ * ‖v‖ ≤ 1 := by
      simpa only [mul_one] using
        mul_le_mul hz' hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [hi, hd, hp]
  simpa only [one_pow, div_one] using CauchyBounds.norm_iteratedDeriv_le n ha hb
    (r := 1) (c := 0) (by norm_num) (by norm_num)

theorem scaledCellSourcePacket_first16 {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u : FieldL2} (hu : ‖u‖ ≤ 1) {k v : Momentum}
    (hi : ‖sourceImaginary k‖ ≤ 8) (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun z : ℂ => scaledCellSourcePacket h u (k + z • v)) 0‖ ≤
      (2 : ℝ)^576 := by
  apply (scaledCellSourcePacket_iteratedDeriv_le hh hh1 hu hi hv n).trans
  have hf : (n.factorial : ℝ) ≤ (Nat.factorial 16 : ℝ) := by
    exact_mod_cast Nat.factorial_le hn
  calc
    _ ≤ (Nat.factorial 16 : ℝ)*(2 : ℝ)^512 :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ ≤ _ := by norm_num

#print axioms scaledCellSourcePacket_first16

end Maxwell.Continuum.CellGauge
