import Maxwell.Continuum.CalibrationFixedPower

/-! A quantitative lower norm for the actual perturbed finite power.
It pays for executable rational normalization of the final Fourier array. -/

noncomputable section
namespace Maxwell.Continuum.Calibration

open EffectiveMass NormedSpace

attribute [local irreducible] Sh muH realMode Bloch.unitary Auxiliary.resolvent
  startingVector powerOperator powerValue startingCoefficient powerIterate

theorem fixed_power_norm_lower {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (N n extra : ℕ) (T : FieldL2 →L[ℂ] FieldL2)
    (w : FieldL2)
    (hT : ‖T-powerOperator D‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra)
    (hw : ‖w-startingVector D.h_pos‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra) :
    (1/2 : ℝ)^(49+38*n) ≤ ‖(T^n) w‖ := by
  have herr : ‖(T^n) w-powerIterate D n‖ ≤
      (2 : ℝ)^(n+1)*(1/2 : ℝ)^powerWorkBits N n extra := by
    rw [powerIterate]
    apply (fixed_power_error (powerOperator D) T (powerOperator_norm D hh) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) hT
      (startingVector D.h_pos) w (le_of_eq (startingVector_norm D.h_pos hh)) hw n).trans
    gcongr
    linarith
  have hd : 0<(1/2 : ℝ)^(48+38*n) := by positivity
  have hb := (div_le_iff₀ hd).mp (fixed_power_work_budget N n extra)
  have heps : (1/2 : ℝ)^(N+10) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hepsmul := mul_le_mul_of_nonneg_right heps hd.le
  have hl := powerIterate_norm_lower D hh n
  have ht := norm_le_norm_sub_add (powerIterate D n) ((T^n) w)
  rw [norm_sub_rev] at ht
  have hp : (1/2 : ℝ)^(49+38*n)=(1/2 : ℝ)^(48+38*n)/2 := by
    rw [show 49+38*n=(48+38*n)+1 by omega,pow_succ]
    ring
  rw [hp]
  nlinarith

#print axioms fixed_power_norm_lower
end Maxwell.Continuum.Calibration
