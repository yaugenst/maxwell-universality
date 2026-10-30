import Maxwell.Continuum.CellSourcePairing
import Maxwell.Continuum.PeriodicPoleContourGeometry

/-! Uniform norms of actual source contractions in the h-wide complex
momentum tube, with the physical source volume counted explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier EffectiveMass Bloch Auxiliary AlmostAnalytic

theorem sourceImaginary_star (q : Momentum) : sourceImaginary (star q) = -sourceImaginary q := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, PiLp.toLp_apply, Pi.star_apply, Complex.star_def,
    Complex.conj_im, PiLp.neg_apply]

theorem cellSourcePacket_tube_norm {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u : FieldL2} (hu : ‖u‖ ≤ 1) {q : Momentum} (hq : ‖sourceImaginary q‖ ≤ h) :
    ‖cellSourcePacket h u q‖ ≤ (2 : ℝ)^40*Real.sqrt ((ballCells h⁻¹).card : ℝ) := by
  have hi : 24*h⁻¹*‖sourceImaginary q‖ ≤ 24 := by
    calc
      _ ≤ 24*h⁻¹*h := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by field_simp
  have he : Real.exp (24 : ℝ) ≤ (2 : ℝ)^40 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 24
    have ht : Real.exp (24 : ℝ) ≤ (3 : ℝ)^24 := by
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
    exact ht.trans (by norm_num)
  apply (cellSourcePacket_norm_le hh hh1 u q).trans
  calc
    _ ≤ ((2 : ℝ)^40*Real.sqrt ((ballCells h⁻¹).card : ℝ))*1 := by
      apply mul_le_mul _ hu (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hi).trans he) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

theorem cellSource_inner_tube_norm {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u v : FieldL2} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {q : Momentum}
    (hq : ‖sourceImaginary q‖ ≤ h) (T : CellMap) :
    ‖inner ℂ (cellSourcePacket h u (star q)) (T (cellSourcePacket h v q))‖ ≤
      (2 : ℝ)^90*(h⁻¹)^3*‖T‖ := by
  have hs : ‖sourceImaginary (star q)‖ ≤ h := by rw [sourceImaginary_star, norm_neg]; exact hq
  have hu' := cellSourcePacket_tube_norm hh hh1 hu hs
  have hv' := cellSourcePacket_tube_norm hh hh1 hv hq
  have hc := ballCells_card_le ((one_le_inv₀ hh).mpr hh1)
  calc
    _ ≤ ‖cellSourcePacket h u (star q)‖*(‖T‖*‖cellSourcePacket h v q‖) :=
      (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _))
    _ ≤ ((2 : ℝ)^40*Real.sqrt ((ballCells h⁻¹).card : ℝ))*
        (‖T‖*((2 : ℝ)^40*Real.sqrt ((ballCells h⁻¹).card : ℝ))) := by gcongr
    _ = (2 : ℝ)^80*((ballCells h⁻¹).card : ℝ)*‖T‖ := by
      calc
        _ = ((2 : ℝ)^40*(2 : ℝ)^40)*(Real.sqrt ((ballCells h⁻¹).card : ℝ))^2*‖T‖ := by ring
        _ = _ := by rw [← pow_add, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ ≤ (2 : ℝ)^80*((2 : ℝ)^10*(h⁻¹)^3)*‖T‖ := by gcongr
    _ = _ := by rw [show (90 : ℕ) = 80+10 by omega, pow_add]; ring

theorem cellSourcePairing_tube_norm {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {u v : FieldL2} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {q : Momentum}
    (hq : ‖sourceImaginary q‖ ≤ h) (Y : Momentum → CellMap) :
    ‖cellSourcePairing h u v Y q‖ ≤ (2 : ℝ)^90*(h⁻¹)^3*‖Y q‖ := by
  rw [cellSourcePairing_eq_inner]
  exact cellSource_inner_tube_norm hh hh1 hu hv hq _

theorem sourceImaginary_shifted (q β : Space) (s : ℝ) :
    sourceImaginary (AlmostAnalytic.shiftedMomentum q β s) = s • β := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, AlmostAnalytic.shiftedMomentum, realMomentumMap,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Complex.ofRealCLM_apply, PiLp.toLp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, one_mul, zero_add, PiLp.smul_apply]

theorem sourceImaginary_poleContour {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (q : Space) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖sourceImaginary (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s)‖ ≤ h := by
  rw [sourceImaginary_shifted, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact (mul_le_mul hs.2 (poleContourShift_norm_le D hh j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

#print axioms cellSourcePairing_tube_norm

end Maxwell.Continuum.CellGauge
