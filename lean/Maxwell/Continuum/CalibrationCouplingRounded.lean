import Maxwell.Continuum.CalibrationCouplingInterval
import Maxwell.Continuum.FiniteAuxiliaryMessageFormat
import Maxwell.Continuum.RationalFiniteWidths

/-! The actual coupling enclosure after executable dyadic center
rounding, with a fixed output denominator and linear operand widths. -/

namespace Maxwell.Continuum.Calibration

open Auxiliary EffectiveMass MasterConstants RationalWords
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def roundedCouplingCenter (q : ℚ) (N : ℕ) : Dyadic (N+6) := roundDyadic (N+6) q
def roundedCouplingInterval (q : ℚ) (N : ℕ) : RationalInterval :=
  couplingInterval (roundedCouplingCenter q N).value N

theorem roundedCouplingInterval_width (q : ℚ) (N : ℕ) :
    (roundedCouplingInterval q N).width = (1/2 : ℚ)^N := couplingInterval_width _ _

theorem roundedCoupling_center_error {q : ℚ} {x : ℝ} (N : ℕ)
    (hq : |(q : ℝ)-x| ≤ (1/2 : ℝ)^(N+6)) :
    |((roundedCouplingCenter q N).value : ℝ)-x| ≤ (1/2 : ℝ)^(N+5) := by
  have hr := roundDyadic_error (N+6) q
  rw [abs_sub_comm] at hr
  have ht := abs_sub_le (((roundedCouplingCenter q N).value : ℝ)) (q : ℝ) x
  have he : 2*(1/2 : ℝ)^(N+6) = (1/2 : ℝ)^(N+5) := by
    rw [show N+6 = (N+5)+1 by omega, pow_succ]
    ring
  rw [← he]
  change |((roundedCouplingCenter q N).value : ℝ)-(q : ℝ)| ≤ _ at hr
  linarith only [ht, hr, hq]

theorem usefulCoupling_rounded_interval {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) (N ℓ : ℕ)
    (hbinary : (L : ℝ) ≤ (2 : ℝ)^ℓ)
    (B : FieldL2 →L[ℂ] FieldL2) (v : FieldL2) (q : ℚ)
    (hv : ‖v-realMode D (inverse_length_le_1024 hL)‖ ≤ (1/2 : ℝ)^(N+2*ℓ+8))
    (hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖ ≤
      (1/2 : ℝ)^(N+5))
    (hq : |(q : ℝ)-(inner ℂ v (B v)).re| ≤ (1/2 : ℝ)^(N+6)) :
    (roundedCouplingInterval q N).Contains (usefulCoupling hL D d j) :=
  usefulCoupling_interval hL D d j N ℓ hbinary B v (roundedCouplingCenter q N).value
    hv hB (roundedCoupling_center_error N hq)

theorem roundedCouplingCenter_bits {q : ℚ} {R : ℕ} (hq : |q| ≤ (2 : ℚ)^R) (N : ℕ) :
    (roundedCouplingCenter q N).numerator.natAbs.bits.length ≤ R+N+8 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (FiniteAuxiliary.roundDyadic_fits hq)

theorem roundedCouplingCenter_width {q : ℚ} {R : ℕ} (hq : |q| ≤ (2 : ℚ)^R) (N : ℕ) :
    Width (roundedCouplingCenter q N).value (R+N+8) := by
  have hn := roundedCouplingCenter_bits hq N
  have hd : (2^(N+6)).bits.length ≤ R+N+8 := by
    rw [Nat.size_eq_bits_len, Nat.size_pow]
    omega
  simpa only [Dyadic.value, Nat.cast_pow, Nat.cast_ofNat] using
    width_fraction (by positivity) hn hd

theorem roundedCouplingInterval_endpoint_width {q : ℚ} {R : ℕ}
    (hq : |q| ≤ (2 : ℚ)^R) (N : ℕ) :
    Width (roundedCouplingInterval q N).lo (R+3*N+12) ∧
    Width (roundedCouplingInterval q N).hi (R+3*N+12) := by
  have hc := roundedCouplingCenter_width hq N
  have hhalf : Width (1/2 : ℚ) 2 := by
    simpa only [one_div] using width_two.inv (by norm_num)
  have hp := hhalf.pow (N+1)
  exact ⟨(hc.sub hp).mono (by omega), (hc.add hp).mono (by omega)⟩

#print axioms usefulCoupling_rounded_interval
#print axioms roundedCouplingInterval_endpoint_width

end Maxwell.Continuum.Calibration
