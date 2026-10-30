import Maxwell.Continuum.MasterConstants
import Maxwell.Continuum.PeriodicPhysicalBand
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Fully symbolic ceiling and cube-root estimates for the nested
momentum scale. No master constant or physical array is expanded. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open MasterConstants PeriodicBand

def leakageDepth (L : ℝ) : ℕ := ⌈L^(1/3 : ℝ)⌉₊

def leakageStep (L : ℝ) : ℝ := smallRadius/(4*(leakageDepth L : ℝ))

theorem leakageDepth_bounds {L : ℝ} (hL : 1 ≤ L) :
    0 < leakageDepth L ∧ L^(1/3 : ℝ) ≤ (leakageDepth L : ℝ) ∧
      (leakageDepth L : ℝ) ≤ 2*L^(1/3 : ℝ) := by
  have hr : 1 ≤ L^(1/3 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlo : L^(1/3 : ℝ) ≤ (leakageDepth L : ℝ) := Nat.le_ceil _
  have hup : (leakageDepth L : ℝ) < L^(1/3 : ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hk : (0 : ℝ) < leakageDepth L := by linarith
  exact ⟨by exact_mod_cast hk, hlo, by linarith⟩

theorem leakageStep_pos {L : ℝ} (hL : 1 ≤ L) : 0 < leakageStep L := by
  have hk : (0 : ℝ) < leakageDepth L := by exact_mod_cast (leakageDepth_bounds hL).1
  exact div_pos smallRadius_pos (by positivity)

theorem leakageStep_endpoint {L : ℝ} (hL : 1 ≤ L) :
    (leakageDepth L : ℝ)*leakageStep L = smallRadius/4 := by
  have hk : (leakageDepth L : ℝ) ≠ 0 := by exact_mod_cast (leakageDepth_bounds hL).1.ne'
  unfold leakageStep
  field_simp

theorem leakage_quarter_decay {L : ℝ} (hL : 1 ≤ L) :
    (1/4 : ℝ)^(leakageDepth L) ≤ Real.exp (-cs*L^(1/3 : ℝ)) := by
  have hc : cs ≤ 1 := by norm_num [cs]
  have hq : (1/4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_three] : Real.exp 1 ≤ 4)
  calc
    _ ≤ Real.exp (-1)^(leakageDepth L) := pow_le_pow_left₀ (by norm_num) hq _
    _ = Real.exp (-(leakageDepth L : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-cs*L^(1/3 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ L^(1/3 : ℝ))
      have hk := (leakageDepth_bounds hL).2.1
      linarith

theorem leakage_sqrt_decay {L : ℝ} (hL : 1 ≤ L) :
    Real.exp (-Real.sqrt (leakageStep L/L⁻¹)/512) ≤ Real.exp (-cs*L^(1/3 : ℝ)) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hr : 0 ≤ L^(1/3 : ℝ) := by positivity
  have hr3 : (L^(1/3 : ℝ))^3 = L := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hLp.le (by norm_num : (3 : ℕ) ≠ 0)
  have hk : (0 : ℝ) < leakageDepth L := by exact_mod_cast (leakageDepth_bounds hL).1
  have hku := (leakageDepth_bounds hL).2.2
  have hc : 8*(512*cs)^2 ≤ smallRadius := by
    norm_num [cs, smallRadius, FreeFiber.backgroundAmplitude]
  have hs : (512*cs*L^(1/3 : ℝ))^2 ≤ leakageStep L/L⁻¹ := by
    rw [leakageStep, div_inv_eq_mul, div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4*(leakageDepth L : ℝ))).mpr
    calc
      (512*cs*L^(1/3 : ℝ))^2 * (4*(leakageDepth L : ℝ)) ≤
          (512*cs*L^(1/3 : ℝ))^2 * (8*L^(1/3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ = (8*(512*cs)^2)*(L^(1/3 : ℝ))^3 := by ring
      _ = (8*(512*cs)^2)*L := by rw [hr3]
      _ ≤ smallRadius*L := mul_le_mul_of_nonneg_right hc hLp.le
  have hsqrt := Real.le_sqrt_of_sq_le hs
  apply Real.exp_le_exp.mpr
  linarith

theorem leakage_twice_sqrt_decay {L : ℝ} (hL : 1 ≤ L) :
    Real.exp (-Real.sqrt ((2*leakageStep L)/L⁻¹)/512) ≤ Real.exp (-cs*L^(1/3 : ℝ)) := by
  apply le_trans _ (leakage_sqrt_decay hL)
  apply Real.exp_le_exp.mpr
  have hΔ := (leakageStep_pos hL).le
  have hi : 0 ≤ L⁻¹ := inv_nonneg.mpr (zero_le_one.trans hL)
  have hs : leakageStep L/L⁻¹ ≤ (2*leakageStep L)/L⁻¹ := by gcongr; linarith
  have hsq := Real.sqrt_le_sqrt hs
  linarith

#print axioms leakage_quarter_decay
#print axioms leakage_sqrt_decay

end Maxwell.Continuum.Auxiliary
