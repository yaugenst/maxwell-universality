import Maxwell.Continuum.AuxiliaryEnergy
import Mathlib.Algebra.Order.Floor.Semiring

/-! The manuscript's explicit master constants, with symbolic power
comparison. Only the 40-bit exponent is evaluated; no tower-sized
integer or gigantic geometric array is constructed. -/

noncomputable section

namespace Maxwell.Continuum.MasterConstants

open Auxiliary FreeFiber

/-- The displayed exponent log₂ Cs. -/
def exponent : ℕ := 2^40

def Cs : ℝ := (2 : ℝ)^exponent

def cs : ℝ := ((2 : ℝ)^1024)⁻¹

def cu : ℝ := ((2 : ℝ)^1024)⁻¹

def lengthExponent : ℕ := ⌈(64 * (exponent : ℝ))/3⌉₊

def Ls : ℝ := (8 : ℝ)^lengthExponent

def ds : ℝ := Cs^8

theorem exponent_large : 8192 ≤ exponent := by norm_num [exponent]

theorem Cs_pos : 0 < Cs := by unfold Cs; positivity

theorem Cs_ge_one : 1 ≤ Cs := one_le_pow₀ (by norm_num)

theorem cs_pos : 0 < cs := by unfold cs; positivity

theorem Ls_pos : 0 < Ls := by unfold Ls; positivity

theorem lengthExponent_covers : 64 * exponent ≤ 3 * lengthExponent := by
  have hc := Nat.le_ceil ((64 * (exponent : ℝ))/3)
  change (64 * (exponent : ℝ))/3 ≤ (lengthExponent : ℝ) at hc
  exact_mod_cast (show (64 : ℝ) * exponent ≤ 3 * lengthExponent by linarith)

theorem Ls_eq_two_pow : Ls = (2 : ℝ)^(3 * lengthExponent) := by
  unfold Ls
  rw [show (8 : ℝ) = 2^3 by norm_num, ← pow_mul]

theorem Cs_pow64_le_Ls : Cs^64 ≤ Ls := by
  rw [Cs, ← pow_mul, Ls_eq_two_pow]
  exact pow_le_pow_right₀ (by norm_num) (by simpa only [Nat.mul_comm] using lengthExponent_covers)

theorem power_le_Ls {n : ℕ} (hn : n ≤ 64 * exponent) : (2 : ℝ)^n ≤ Ls := by
  rw [Ls_eq_two_pow]
  exact pow_le_pow_right₀ (by norm_num) (hn.trans lengthExponent_covers)

theorem power_lt_Ls {n : ℕ} (hn : n < 64 * exponent) : (2 : ℝ)^n < Ls := by
  rw [Ls_eq_two_pow]
  exact pow_lt_pow_right₀ (by norm_num) (hn.trans_le lengthExponent_covers)

theorem length_pos {L : ℝ} (hL : Ls ≤ L) : 0 < L := Ls_pos.trans_le hL

theorem length_ge_one {L : ℝ} (hL : Ls ≤ L) : 1 ≤ L := by
  have h := (power_le_Ls (n := 0) (by omega)).trans hL
  simpa only [pow_zero] using h

theorem inverse_length_pos {L : ℝ} (hL : Ls ≤ L) : 0 < L⁻¹ := inv_pos.mpr (length_pos hL)

theorem inverse_length_le_power {L : ℝ} (hL : Ls ≤ L) {n : ℕ} (hn : n ≤ 64 * exponent) :
    L⁻¹ ≤ ((2 : ℝ)^n)⁻¹ :=
  (inv_le_inv₀ (length_pos hL) (by positivity)).mpr ((power_le_Ls hn).trans hL)

theorem inverse_length_lt_power {L : ℝ} (hL : Ls ≤ L) {n : ℕ} (hn : n < 64 * exponent) :
    L⁻¹ < ((2 : ℝ)^n)⁻¹ :=
  (inv_lt_inv₀ (length_pos hL) (by positivity)).mpr ((power_lt_Ls hn).trans_le hL)

theorem inverse_length_le_1024 {L : ℝ} (hL : Ls ≤ L) : L⁻¹ ≤ 1/(2 : ℝ)^1024 := by
  simpa only [one_div] using inverse_length_le_power hL (n := 1024) (by have := exponent_large; omega)

theorem inverse_length_le_amplitude {L : ℝ} (hL : Ls ≤ L) : L⁻¹ ≤ backgroundAmplitude := by
  have hp := inverse_length_le_power hL (n := 100) (by have := exponent_large; omega)
  simpa only [backgroundAmplitude, one_div] using hp

theorem fixed_power_le_Cs {n : ℕ} (hn : n ≤ exponent) : (2 : ℝ)^n ≤ Cs :=
  pow_le_pow_right₀ (by norm_num) hn

theorem H1_constant_le_Cs : (2 : ℝ)^512 ≤ Cs :=
  fixed_power_le_Cs (by have := exponent_large; omega)

theorem spatial_constant_le_Cs : (2 : ℝ)^2048 ≤ Cs :=
  fixed_power_le_Cs (by have := exponent_large; omega)

theorem power_times_inverse_length_lt {L : ℝ} (hL : Ls ≤ L) {a b : ℕ}
    (hab : a + b < 64 * exponent) :
    (2 : ℝ)^a * L⁻¹ < ((2 : ℝ)^b)⁻¹ := by
  calc
    _ < (2 : ℝ)^a * ((2 : ℝ)^(a+b))⁻¹ :=
      mul_lt_mul_of_pos_left (inverse_length_lt_power hL hab) (by positivity)
    _ = _ := by
      rw [pow_add, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (by positivity : (2 : ℝ)^a ≠ 0), mul_one]

theorem effective_comparison_small {L : ℝ} (hL : Ls ≤ L) :
    (2 : ℝ)^520 * L⁻¹ < ((2 : ℝ)^200)⁻¹ :=
  power_times_inverse_length_lt hL (by have := exponent_large; omega)

theorem separated_error_small {L : ℝ} (hL : Ls ≤ L) :
    (2 : ℝ)^112 * (L⁻¹)^2 < ((2 : ℝ)^200)⁻¹ := by
  have hh : L⁻¹ ≤ 1 := by
    have := inverse_length_le_power hL (n := 0) (by omega)
    simpa only [pow_zero, inv_one] using this
  have hsq : (L⁻¹)^2 ≤ L⁻¹ := by nlinarith [inverse_length_pos hL]
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans_lt
    (power_times_inverse_length_lt hL (a := 112) (b := 200) (by have := exponent_large; omega))

theorem calibration_of_length {L z : ℝ} (hL : Ls ≤ L)
    (hz : |z - (centerEnergy - (L⁻¹)^2)| ≤ (L⁻¹)^4) : Calibration L⁻¹ z :=
  ⟨inverse_length_pos hL, inverse_length_le_amplitude hL, hz⟩

#print axioms Cs_pow64_le_Ls
#print axioms inverse_length_le_1024
#print axioms effective_comparison_small
#print axioms separated_error_small

end Maxwell.Continuum.MasterConstants
