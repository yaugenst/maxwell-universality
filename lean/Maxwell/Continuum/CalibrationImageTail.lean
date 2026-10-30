import Maxwell.Continuum.CalibrationLatticeDecay
import Maxwell.Continuum.MasterConstants

/-! The explicit master constant absorbs the complete periodic-image tail.
All large powers remain symbolic. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Calibration

open MasterConstants

theorem cs_quarter_inverse : (cs/4)⁻¹ = (2 : ℝ)^1026 := by
  rw [inv_div, cs, div_inv_eq_mul]
  calc
    (4 : ℝ) * 2^1024 = 2^2 * 2^1024 := by norm_num
    _ = _ := by rw [← pow_add]

theorem image_tail_constant_le : (2 : ℝ)^32 * (64*latticeDecayConstant (cs/4)) ≤ Cs := by
  have hf : ((12 : ℕ).factorial : ℝ) ≤ (2 : ℝ)^32 := by norm_num
  have he : (2 : ℝ)^32 * (64*latticeDecayConstant (cs/4)) =
      ((12 : ℕ).factorial : ℝ) * (2 : ℝ)^12356 := by
    unfold latticeDecayConstant
    rw [div_eq_mul_inv, ← inv_pow, cs_quarter_inverse]
    calc
      _ = ((12 : ℕ).factorial : ℝ) * ((2 : ℝ)^32 * (64*64)) * ((2 : ℝ)^1026)^12 := by ring
      _ = ((12 : ℕ).factorial : ℝ) * ((2 : ℝ)^44) * ((2 : ℝ)^1026)^12 := by norm_num
      _ = _ := by rw [← pow_mul, mul_assoc, ← pow_add]
  rw [he]
  calc
    _ ≤ (2 : ℝ)^32 * 2^12356 := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = (2 : ℝ)^12388 := by rw [← pow_add]
    _ ≤ Cs := fixed_power_le_Cs (by norm_num [exponent])

theorem image_tail_prefactor_le : 64*latticeDecayConstant (cs/4) ≤ Cs/(2 : ℝ)^32 :=
  (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using image_tail_constant_le)

theorem image_decay_parameter {L M : ℝ} (hL : 0 < L) (hM : L ≤ M) :
    2*(cs/4) ≤ (cs/2)*Real.sqrt (M/L) := by
  have hr : (1 : ℝ) ≤ M/L := (le_div_iff₀ hL).mpr (by simpa using hM)
  have hs : 1 ≤ Real.sqrt (M/L) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  nlinarith [cs_pos]

theorem image_tail_sum {L M : ℝ} (hL : 0 < L) (hM : L ≤ M) :
    Summable (imageTail ((cs/2)*Real.sqrt (M/L))) ∧
    ∑' j : Fin 3 → ℤ, imageTail ((cs/2)*Real.sqrt (M/L)) j ≤
      (Cs/(2 : ℝ)^32)*Real.exp (-(cs/4)*Real.sqrt (M/L)) := by
  have hb : 0 < cs/4 := div_pos cs_pos (by norm_num)
  have ha := image_decay_parameter hL hM
  refine ⟨imageTail_summable hb ha, ?_⟩
  calc
    _ ≤ 64*latticeDecayConstant (cs/4)*
        Real.exp (-((cs/2)*Real.sqrt (M/L))/2) := imageTail_tsum_bound hb ha
    _ ≤ (Cs/(2 : ℝ)^32)*Real.exp (-((cs/2)*Real.sqrt (M/L))/2) :=
      mul_le_mul_of_nonneg_right image_tail_prefactor_le (Real.exp_pos _).le
    _ = _ := by rw [show -((cs/2)*Real.sqrt (M/L))/2 = -(cs/4)*Real.sqrt (M/L) by ring]

theorem image_distance_decay {L M r : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (j : Fin 3 → ℤ) (hj : j ≠ 0) (hr : M*(imageRadius j : ℝ)/4 ≤ r) :
    Real.exp (-cs*Real.sqrt (r/L)) ≤ imageTail ((cs/2)*Real.sqrt (M/L)) j := by
  rw [imageTail, ite_eq_right hj]
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ M/L := div_nonneg hM hL.le
  have hj0 : (0 : ℝ) ≤ imageRadius j := Nat.cast_nonneg _
  have he : Real.sqrt (M*(imageRadius j : ℝ)/4/L) =
      Real.sqrt (M/L)*Real.sqrt (imageRadius j)/2 := by
    rw [show M*(imageRadius j : ℝ)/4/L = (M/L)*(imageRadius j)/4 by ring,
      Real.sqrt_div (mul_nonneg h0 hj0), Real.sqrt_mul h0]
    norm_num
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hr hL.le)
  rw [he] at hs
  nlinarith [cs_pos]

#print axioms image_tail_sum
#print axioms image_distance_decay

end Maxwell.Continuum.Calibration
