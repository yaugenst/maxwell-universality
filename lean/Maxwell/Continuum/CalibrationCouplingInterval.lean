import Maxwell.Continuum.CalibrationCouplingError
import Maxwell.Continuum.CalibrationInterval

/-! Explicit finite rational enclosures of the actual useful coupling
from the calibrated mode and periodized two-well operator. -/

namespace Maxwell.Continuum.Calibration

open Auxiliary EffectiveMass MasterConstants
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def couplingInterval (c : ℚ) (N : ℕ) : RationalInterval :=
  ⟨c-(1/2 : ℚ)^(N+1), c+(1/2 : ℚ)^(N+1), by
    have h : (0 : ℚ) ≤ (1/2 : ℚ)^(N+1) := by positivity
    linarith only [h]⟩

theorem couplingInterval_width (c : ℚ) (N : ℕ) :
    (couplingInterval c N).width = (1/2 : ℚ)^N := by
  change (c+(1/2 : ℚ)^(N+1))-(c-(1/2 : ℚ)^(N+1)) = _
  rw [pow_succ]
  ring

theorem couplingInterval_midpoint (c : ℚ) (N : ℕ) : (couplingInterval c N).midpoint = c := by
  change ((c-(1/2 : ℚ)^(N+1))+(c+(1/2 : ℚ)^(N+1)))/2 = _
  ring

theorem couplingInterval_contains {c : ℚ} {x : ℝ} {N : ℕ}
    (h : |(c : ℝ)-x| ≤ (1/2 : ℝ)^(N+1)) : (couplingInterval c N).Contains x := by
  have hh := abs_le.mp h
  change ((c-(1/2 : ℚ)^(N+1) : ℚ) : ℝ) ≤ x ∧ x ≤ ((c+(1/2 : ℚ)^(N+1) : ℚ) : ℝ)
  push_cast
  constructor <;> linarith only [hh.1, hh.2]

private theorem coupling_precision_budget {L : ℕ} (N ℓ : ℕ)
    (hL : (L : ℝ) ≤ (2 : ℝ)^ℓ) :
    12*(L : ℝ)^2*(1/2 : ℝ)^(N+2*ℓ+8)+4*(1/2 : ℝ)^(N+5)+(1/2 : ℝ)^(N+5) ≤
      (1/2 : ℝ)^(N+1) := by
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg L) hL 2
  have hm := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ (1/2 : ℝ)^(N+2*ℓ+8) by positivity)
  have he : ((2 : ℝ)^ℓ)^2*(1/2 : ℝ)^(N+2*ℓ+8) = (1/2 : ℝ)^(N+8) := by
    rw [← pow_mul, show ℓ*2 = 2*ℓ by omega,
      show N+2*ℓ+8 = 2*ℓ+(N+8) by omega, pow_add]
    simp only [div_pow, one_pow]
    field_simp
  rw [he] at hm
  have hn : (0 : ℝ) ≤ (1/2 : ℝ)^N := by positivity
  calc
    _ ≤ 12*(1/2 : ℝ)^(N+8)+4*(1/2 : ℝ)^(N+5)+(1/2 : ℝ)^(N+5) := by
      nlinarith only [hm]
    _ ≤ (1/2 : ℝ)^(N+1) := by
      rw [pow_add (1/2 : ℝ) N 8, pow_add (1/2 : ℝ) N 5, pow_add (1/2 : ℝ) N 1]
      norm_num only [show (1/2 : ℝ)^8 = 1/256 by norm_num,
        show (1/2 : ℝ)^5 = 1/32 by norm_num, pow_one]
      nlinarith only [hn]

theorem usefulCoupling_interval {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) (N ℓ : ℕ)
    (hbinary : (L : ℝ) ≤ (2 : ℝ)^ℓ)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (c : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ (1/2 : ℝ)^(N+2*ℓ+8))
    (hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤
      (1/2 : ℝ)^(N+5))
    (hc : |(c : ℝ)-(inner ℂ v (B v)).re| ≤ (1/2 : ℝ)^(N+5)) :
    (couplingInterval c N).Contains (usefulCoupling hL D d j) := by
  have hb := usefulCoupling_approximation hL D d j B v hv
    (pow_le_one₀ (by norm_num) (by norm_num)) hB
  apply couplingInterval_contains
  have ht := abs_add_le ((c : ℝ)-(inner ℂ v (B v)).re)
    ((inner ℂ v (B v)).re-usefulCoupling hL D d j)
  rw [sub_add_sub_cancel] at ht
  exact (ht.trans (add_le_add hc hb)).trans (by
    have hh := coupling_precision_budget N ℓ hbinary
    linarith only [hh])

#print axioms usefulCoupling_interval
#print axioms couplingInterval_width

end Maxwell.Continuum.Calibration
