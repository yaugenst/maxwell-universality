import Maxwell.Continuum.CalibrationPi
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Executable arbitrary-precision rational phase evaluation with logarithmic guard bits. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate

def phaseBits (Q N : ℕ) : ℕ := N+Nat.clog 2 (Q+1)+4

def phaseAngle (q : ℚ) (Q N : ℕ) : ℚ := 2*(Elementary.piApprox (phaseBits Q N)).center*q

theorem phase_guard (Q N : ℕ) :
    2*(Q : ℝ)*(1/2 : ℝ)^phaseBits Q N ≤ (1/2 : ℝ)^(N+3) := by
  have hQ : (Q : ℝ) ≤ (2 : ℝ)^Nat.clog 2 (Q+1) := by
    exact_mod_cast (Nat.le_succ Q).trans (Nat.le_pow_clog (by decide : 1<2) (Q+1))
  calc
    _ ≤ 2*((2 : ℝ)^Nat.clog 2 (Q+1))*(1/2 : ℝ)^phaseBits Q N := by gcongr
    _ = _ := by
      unfold phaseBits
      rw [pow_add, pow_add, pow_add]
      have he : (2 : ℝ)^Nat.clog 2 (Q+1)*(1/2 : ℝ)^Nat.clog 2 (Q+1)=1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = ((1/2 : ℝ)^N*(1/2 : ℝ)^3)*
            ((2 : ℝ)^Nat.clog 2 (Q+1)*(1/2 : ℝ)^Nat.clog 2 (Q+1)) := by ring
        _ = _ := by rw [he, mul_one]

theorem piApprox_center_bound (N : ℕ) : |(Elementary.piApprox N).center| ≤ (5 : ℚ) := by
  have hp := Elementary.piApprox_contains N
  rw [Ball.Contains, Elementary.piApprox_radius] at hp
  push_cast at hp
  have h1 : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr : |((Elementary.piApprox N).center : ℝ)| ≤ 5 := by
    have h := abs_sub_le ((Elementary.piApprox N).center : ℝ) Real.pi 0
    rw [sub_zero, sub_zero, abs_sub_comm _ Real.pi, abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_lt_four]
  exact_mod_cast hr

theorem phaseAngle_bound (q : ℚ) (Q N : ℕ) (hq : |q| ≤ Q) :
    |phaseAngle q Q N| ≤ (10*(Q+1) : ℕ) := by
  unfold phaseAngle
  rw [abs_mul, abs_mul]
  have hp := piApprox_center_bound (phaseBits Q N)
  rw [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℚ) ≤ 2)) hq
    (abs_nonneg q) (by norm_num : (0 : ℚ) ≤ 2*5)
  push_cast
  nlinarith only [hh]

theorem phaseAngle_error (q : ℚ) (Q N : ℕ) (hq : |q| ≤ Q) :
    |2*Real.pi*(q : ℝ)-(phaseAngle q Q N : ℝ)| ≤ (1/2 : ℝ)^(N+3) := by
  have hp := Elementary.piApprox_contains (phaseBits Q N)
  rw [Ball.Contains, Elementary.piApprox_radius] at hp
  push_cast at hp
  have hqr : |(q : ℝ)| ≤ Q := by exact_mod_cast hq
  calc
    _ = 2*|Real.pi-((Elementary.piApprox (phaseBits Q N)).center : ℝ)| * |(q : ℝ)| := by
      simp only [phaseAngle, Rat.cast_mul, Rat.cast_ofNat]
      rw [show 2*Real.pi*(q : ℝ)-2*((Elementary.piApprox (phaseBits Q N)).center : ℝ)*q =
        2*(Real.pi-((Elementary.piApprox (phaseBits Q N)).center : ℝ))*q by ring]
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2*(1/2 : ℝ)^phaseBits Q N*Q := mul_le_mul
      (mul_le_mul_of_nonneg_left hp (by norm_num)) hqr (abs_nonneg _) (by positivity)
    _ = 2*(Q : ℝ)*(1/2 : ℝ)^phaseBits Q N := by ring
    _ ≤ _ := phase_guard Q N

def cosTurnApprox (q : ℚ) (Q N : ℕ) : Ball :=
  ⟨(Elementary.cosApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center,
    (1/2)^N,by positivity⟩

def sinTurnApprox (q : ℚ) (Q N : ℕ) : Ball :=
  ⟨(Elementary.sinApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center,
    (1/2)^N,by positivity⟩

theorem cosTurnApprox_contains (q : ℚ) (Q N : ℕ) (hq : |q| ≤ Q) :
    (cosTurnApprox q Q N).Contains (Real.cos (2*Real.pi*(q : ℝ))) := by
  have ha := Elementary.cosApprox_contains (phaseAngle q Q N) (10*(Q+1)) (N+3)
    (phaseAngle_bound q Q N hq)
  rw [Ball.Contains, (Elementary.elementary_radii _ _ _).2.1] at ha
  push_cast at ha
  have he := (Real.abs_cos_sub_cos_le (2*Real.pi*(q : ℝ)) (phaseAngle q Q N)).trans
    (phaseAngle_error q Q N hq)
  change |Real.cos (2*Real.pi*(q : ℝ))-
    ((Elementary.cosApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center : ℝ)| ≤ _
  calc
    _ ≤ |Real.cos (2*Real.pi*(q : ℝ))-Real.cos (phaseAngle q Q N)|+
        |Real.cos (phaseAngle q Q N)-((Elementary.cosApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center : ℝ)| := abs_sub_le _ _ _
    _ ≤ 2*(1/2 : ℝ)^(N+3) := by linarith
    _ ≤ _ := by
      change 2*(1/2 : ℝ)^(N+3) ≤ (((1/2 : ℚ)^N : ℚ) : ℝ)
      push_cast
      rw [pow_add]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

theorem sinTurnApprox_contains (q : ℚ) (Q N : ℕ) (hq : |q| ≤ Q) :
    (sinTurnApprox q Q N).Contains (Real.sin (2*Real.pi*(q : ℝ))) := by
  have ha := Elementary.sinApprox_contains (phaseAngle q Q N) (10*(Q+1)) (N+3)
    (phaseAngle_bound q Q N hq)
  rw [Ball.Contains, (Elementary.elementary_radii _ _ _).2.2] at ha
  push_cast at ha
  have he := (Real.abs_sin_sub_sin_le (2*Real.pi*(q : ℝ)) (phaseAngle q Q N)).trans
    (phaseAngle_error q Q N hq)
  change |Real.sin (2*Real.pi*(q : ℝ))-
    ((Elementary.sinApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center : ℝ)| ≤ _
  calc
    _ ≤ |Real.sin (2*Real.pi*(q : ℝ))-Real.sin (phaseAngle q Q N)|+
        |Real.sin (phaseAngle q Q N)-((Elementary.sinApprox (phaseAngle q Q N) (10*(Q+1)) (N+3)).center : ℝ)| := abs_sub_le _ _ _
    _ ≤ 2*(1/2 : ℝ)^(N+3) := by linarith
    _ ≤ _ := by
      change 2*(1/2 : ℝ)^(N+3) ≤ (((1/2 : ℚ)^N : ℚ) : ℝ)
      push_cast
      rw [pow_add]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

theorem cosTurnApprox_radius (q : ℚ) (Q N : ℕ) : (cosTurnApprox q Q N).radius=(1/2 : ℚ)^N := rfl
theorem sinTurnApprox_radius (q : ℚ) (Q N : ℕ) : (sinTurnApprox q Q N).radius=(1/2 : ℚ)^N := rfl

#print axioms cosTurnApprox_contains
#print axioms sinTurnApprox_contains

end Maxwell.Continuum.Calibration
