import Maxwell.Continuum.CalibrationPower
import Mathlib.Data.Nat.Log

/-! The prescribed work precision controls a sequence of approximate
applications to the actual continuum operator. The application errors
are explicit intermediate hypotheses to be discharged by finite
quadrature and rational evaluation, not a solver oracle definition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open EffectiveMass NormedSpace

attribute [local irreducible] Sh muH realMode Bloch.unitary Auxiliary.resolvent
  startingVector powerOperator powerValue startingCoefficient

def powerWorkPrecision (N : ℕ) : ℕ :=
  powerWorkBits N (powerSteps N) (Nat.clog 2 (powerSteps N+1))

theorem approximate_power_nonzero_and_normalized_error {h z : ℝ}
    (D : Auxiliary.Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (N n extra : ℕ) (hlog : n+1 ≤ 2^extra) (y : ℕ → FieldL2)
    (h0 : ‖y 0-startingVector D.h_pos‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra)
    (hstep : ∀ k, ‖y (k+1)-powerOperator D (y k)‖ ≤ (1/2 : ℝ)^powerWorkBits N n extra) :
    y n ≠ 0 ∧ ‖normalize (y n)-normalize (powerIterate D n)‖ ≤ (1/2 : ℝ)^(N+10) := by
  have herr : ‖y n-powerIterate D n‖ ≤
      ((n : ℝ)+1)*(1/2 : ℝ)^powerWorkBits N n extra :=
    approximate_power_error (powerOperator D) (powerOperator_norm D hh)
      (startingVector D.h_pos) y h0 hstep n
  have hl := powerIterate_norm_lower D hh n
  have hlpos : 0 < (1/2 : ℝ)^(48+38*n) := by positivity
  have hbudget := powerWorkBits_budget N n extra hlog
  have hsmall : (1/2 : ℝ)^(N+10) ≤ 1/1024 := by
    have hb := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) (by omega : 10 ≤ N+10)
    norm_num at hb
    exact hb
  have hbprod := (div_le_iff₀ hlpos).mp hbudget
  have herrlt : ‖y n-powerIterate D n‖ < (1/2 : ℝ)^(48+38*n) := by
    have hp := mul_le_mul_of_nonneg_right hsmall hlpos.le
    nlinarith
  have hy : y n ≠ 0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at herrlt
    linarith
  refine ⟨hy,?_⟩
  have hn := normalize_difference (y n) (powerIterate D n) hy (powerIterate_ne_zero D hh n)
  apply hn.trans
  apply le_trans _ hbudget
  apply div_le_div₀ (by positivity) _ hlpos hl
  exact (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (mul_assoc _ _ _).symm

theorem approximate_power_requested_error {h z : ℝ}
    (D : Auxiliary.Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (N : ℕ) (y : ℕ → FieldL2)
    (h0 : ‖y 0-startingVector D.h_pos‖ ≤ (1/2 : ℝ)^powerWorkPrecision N)
    (hstep : ∀ k, ‖y (k+1)-powerOperator D (y k)‖ ≤ (1/2 : ℝ)^powerWorkPrecision N) :
    y (powerSteps N) ≠ 0 ∧
      ‖normalize (y (powerSteps N))-realMode D hh‖ ≤ (1/2 : ℝ)^N := by
  have hb := approximate_power_nonzero_and_normalized_error D hh N (powerSteps N)
    (Nat.clog 2 (powerSteps N+1)) (Nat.le_pow_clog (by norm_num) _) y h0 hstep
  refine ⟨hb.1,?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub (normalize (y (powerSteps N)))
    (normalize (powerIterate D (powerSteps N))) (realMode D hh)
  apply (ht.trans (add_le_add hb.2 (powerIterate_requested_error D hh N))).trans
  rw [pow_add,pow_add]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

#print axioms approximate_power_nonzero_and_normalized_error
#print axioms approximate_power_requested_error

end Maxwell.Continuum.Calibration
