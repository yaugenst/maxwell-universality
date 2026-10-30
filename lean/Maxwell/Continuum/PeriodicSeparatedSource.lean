import Maxwell.Continuum.PeriodicGlobalSeparated
import Maxwell.Continuum.PeriodicGlobalNumerator
import Maxwell.Continuum.CellSourcePairing
import Maxwell.Continuum.CellSourcePacketDerivatives

/-! The literal other-band inverse contracted with the actual continuum
source packets. Its holomorphy and derivative bounds preserve the h² factor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass CellGauge Set Metric

attribute [local irreducible] separatedCellSymbol poleMomentum imaginaryPole realMode

def separatedSourceSymbol {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (k : Momentum) : ℂ :=
  inner ℂ (scaledCellSourcePacket h u (star (scaledPoleCenter D hh j+k)))
    (scaledSeparatedCell D hh j k (scaledCellSourcePacket h v (scaledPoleCenter D hh j+k)))

theorem separatedSourceSymbol_eq_pairing {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (k : Momentum) :
    separatedSourceSymbol D hh j u v k = ((h^2*(sourceScale h)^2 : ℝ) : ℂ)*
      cellSourcePairing h u v (separatedCellSymbol z 0) (poleMomentum D hh j k) := by
  rw [cellSourcePairing_eq_inner]
  have hs : (h : ℂ) • star (scaledPoleCenter D hh j+k) = star (poleMomentum D hh j k) := by
    rw [← scaledPoleCenter_physical]
    simp only [star_smul, Complex.star_def, Complex.conj_ofReal]
  unfold separatedSourceSymbol scaledCellSourcePacket scaledSeparatedCell
  rw [scaledPoleCenter_physical, hs, smul_apply, map_smul,
    inner_smul_left, inner_smul_right, inner_smul_right]
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  have he (a b : ℝ) (c : ℂ) : (a : ℂ)*((b : ℂ)*((a : ℂ)*c)) = ((b*a^2 : ℝ) : ℂ)*c := by
    push_cast
    ring
  exact he (sourceScale h) (h^2) _

theorem separatedSourceSymbol_analyticAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) {k : Momentum}
    (hk : ‖poleMomentum D hh j k‖ ≤ separatedRadius) :
    AnalyticAt ℂ (separatedSourceSymbol D hh j u v) k := by
  change AnalyticAt ℂ (fun p => separatedSourceSymbol D hh j u v p) k
  simp_rw [separatedSourceSymbol_eq_pairing]
  have hs := cellSourcePairing_analytic h u v
    (separatedCellSymbol_analytic D le_rfl (by positivity) _
      (by simpa only [mem_closedBall, dist_zero_right] using hk))
  have hp : AnalyticAt ℂ (poleMomentum D hh j) k := by
    unfold poleMomentum
    exact analyticAt_const.add (analyticAt_id.const_smul (c := (h : ℂ)))
  convert! AnalyticAt.mul analyticAt_const (hs.comp (f := poleMomentum D hh j) hp) using 1

theorem sourceImaginary_star (k : Momentum) : sourceImaginary (star k) = -sourceImaginary k := by
  apply PiLp.ext
  intro i
  change (star (k i)).im = -(k i).im
  exact Complex.conj_im _

theorem globalPole_source_line_imaginary {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    {v : Momentum} (hv : ‖v‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1/16) :
    ‖sourceImaginary (scaledPoleCenter D hh j+(realMomentum k.ofLp+ζ • v))‖ ≤ 10 := by
  rw [← add_assoc, sourceImaginary_add]
  apply (norm_add_le _ _).trans
  have hi := globalPole_source_imaginary D hh j k
  have hz := sourceImaginary_norm_le (ζ • v)
  rw [norm_smul] at hz
  have hp : ‖ζ‖*‖v‖ ≤ 1/16 := by
    simpa only [mul_one] using mul_le_mul hζ hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/16)
  linarith only [hi, hz, hp]

theorem separatedSourceSymbol_line_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : Space) (hk : h*‖k‖ ≤ 4*smallRadius)
    {w : Momentum} (hw : ‖w‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1/16) :
    ‖separatedSourceSymbol D hh j u v (realMomentum k.ofLp+ζ • w)‖ ≤ (2 : ℝ)^1140*h^2 := by
  have hh1 : h ≤ 1 := hh.trans (by norm_num)
  have hi := globalPole_source_line_imaginary D hh j k hw hζ
  have ha := scaledCellSourcePacket_norm_ledger D.h_pos hh1 hu
    (k := star (scaledPoleCenter D hh j+(realMomentum k.ofLp+ζ • w)))
    (by simpa only [sourceImaginary_star, norm_neg] using hi)
  have hb := scaledCellSourcePacket_norm_ledger D.h_pos hh1 hv hi
  have hc := scaledSeparatedCell_line_norm D hh j k hk hw hζ
  unfold separatedSourceSymbol
  calc
    _ ≤ ‖scaledCellSourcePacket h u (star (scaledPoleCenter D hh j+(realMomentum k.ofLp+ζ • w)))‖ *
        ‖scaledSeparatedCell D hh j (realMomentum k.ofLp+ζ • w)
          (scaledCellSourcePacket h v (scaledPoleCenter D hh j+(realMomentum k.ofLp+ζ • w)))‖ :=
      norm_inner_le_norm _ _
    _ ≤ (2 : ℝ)^512*((2 : ℝ)^116*h^2*(2 : ℝ)^512) := by
      apply mul_le_mul ha _ (norm_nonneg _) (by positivity)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hc hb (norm_nonneg _) (by positivity))
    _ = _ := by rw [show 1140 = 512+116+512 by omega, pow_add, pow_add]; ring

theorem separatedSourceSymbol_line_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2)
    (k : Space) (hk : h*‖k‖ ≤ 4*smallRadius) {w : Momentum} (hw : ‖w‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => separatedSourceSymbol D hh j u v
      (realMomentum k.ofLp+ζ • w)) (closedBall 0 (1/16)) := by
  intro ζ hζ
  exact (separatedSourceSymbol_analyticAt D hh j u v
    (globalPole_unit_line_chart D hh j k hk hw
      (by simpa only [mem_closedBall, dist_zero_right] using hζ))).comp
    (f := fun ζ : ℂ => realMomentum k.ofLp+ζ • w)
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem separatedSourceSymbol_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : Space) (hk : h*‖k‖ ≤ 4*smallRadius)
    {w : Momentum} (hw : ‖w‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun ζ : ℂ => separatedSourceSymbol D hh j u v
      (realMomentum k.ofLp+ζ • w)) 0‖ ≤ (2 : ℝ)^1400*h^2 := by
  have he := CauchyBounds.norm_iteratedDeriv_le n
    (separatedSourceSymbol_line_analytic D hh j u v k hk hw)
    (fun ζ hζ => separatedSourceSymbol_line_norm D hh j hu hv k hk hw
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
    _ ≤ (2 : ℝ)^160*((2 : ℝ)^1140*h^2)*(2 : ℝ)^64 := by gcongr
    _ = (2 : ℝ)^1364*h^2 := by rw [show 1364 = 160+1140+64 by omega, pow_add, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (sq_nonneg h)

#print axioms separatedSourceSymbol_derivative

end Maxwell.Continuum.PeriodicBand
