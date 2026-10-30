import Maxwell.Continuum.CalibrationInterval
import Maxwell.Continuum.ParameterReciprocal
import Maxwell.Continuum.EffectiveMassRealMode
import Maxwell.Realization.ScalarPrecision

/-! Finite rational-interval to dyadic tuning of the continuum wells.
Only rational interval data and rational targets enter the emitted values. -/

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Realization EffectiveMass MasterConstants

def couplingRound (ζ : ℚ) (hζ : 0 < ζ) (I : Calibration.RationalInterval) :=
  selectedRound (ζ^2/16) (by positivity) I.midpoint

theorem couplingRound_error (ζ : ℚ) (hζ : 0 < ζ) (I : Calibration.RationalInterval)
    {x : ℝ} (hx : I.Contains x) (hwidth : I.width ≤ ζ^2/16) :
    |((couplingRound ζ hζ I).value : ℝ)-x| ≤ (ζ : ℝ)^2/16 := by
  have hm := I.midpoint_error hx
  have hw : (I.width : ℝ) ≤ (ζ : ℝ)^2/16 := by exact_mod_cast hwidth
  have he : |((couplingRound ζ hζ I).value : ℝ)-(I.midpoint : ℝ)| ≤ (ζ : ℝ)^2/32 := by
    have h := selectedRound_error (ζ^2/16) (by positivity) I.midpoint
    change |(couplingRound ζ hζ I).value-I.midpoint| ≤ (ζ^2/16)/2 at h
    have hr : |((couplingRound ζ hζ I).value : ℝ)-(I.midpoint : ℝ)| ≤ ((ζ : ℝ)^2/16)/2 := by
      exact_mod_cast h
    convert hr using 1
    ring
  have ht := abs_sub_le ((couplingRound ζ hζ I).value : ℝ) (I.midpoint : ℝ) x
  linarith only [hm, hw, he, ht]

def onsiteRound (L : ℕ) (hL : 0 < L) (ζ : ℚ) (hζ : 0 < ζ)
    (I : Calibration.RationalInterval) (θ : ℚ) :=
  scalarRound ((L : ℚ)⁻¹^2) ζ ((2 : ℚ)^128*(L : ℚ)⁻¹^2)
    (by positivity) hζ (by positivity) (I.midpoint+θ)⁻¹

theorem onsiteRound_bounds {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (hLN : 0 < L)
    (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (I : Calibration.RationalInterval) (θ : ℚ)
    (hI : I.Contains (muH D (inverse_length_le_1024 hL))) (hwidth : I.width ≤ ζ^2/8)
    (hθ : |(θ : ℝ)| ≤ (1/(2 : ℝ)^196)*(L : ℝ)^2) :
    0 < (onsiteRound L hLN ζ hζ I θ).value ∧
    ((onsiteRound L hLN ζ hζ I θ).value : ℝ) ≤ (2 : ℝ)^130*(L : ℝ)⁻¹^2 ∧
    |((onsiteRound L hLN ζ hζ I θ).value : ℝ)⁻¹-
      (muH D (inverse_length_le_1024 hL)+(θ : ℝ))| ≤ (ζ : ℝ)^2 := by
  have hm := I.midpoint_error hI
  have hw : (I.width : ℝ) ≤ (ζ : ℝ)^2/8 := by exact_mod_cast hwidth
  have herr : |(I.midpoint : ℝ)-muH D (inverse_length_le_1024 hL)| ≤ (ζ : ℝ)^2/16 := by
    linarith only [hm, hw]
  have hμ := muH_bounds D (inverse_length_le_1024 hL)
  simp only [inv_pow, inv_inv] at hμ
  have hrec := Parameters.reciprocal_enclosure hL hμ.1 hμ.2 hθ herr
    (by exact_mod_cast hζ.le) (by exact_mod_cast hζ1)
  have hv : (L : ℚ)⁻¹^2 ≤ (I.midpoint+θ)⁻¹ := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hrec.1
  have hvhi : (I.midpoint+θ)⁻¹ ≤ (2 : ℚ)^129*(L : ℚ)⁻¹^2 := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hrec.2
  have hround := scalarRound_bounds ((L : ℚ)⁻¹^2) ζ ((2 : ℚ)^128*(L : ℚ)⁻¹^2)
    (by positivity) hζ (by positivity) (I.midpoint+θ)⁻¹ hv
  have htune := scalarRound_tuning_real ((L : ℚ)⁻¹^2) ζ ((2 : ℚ)^128*(L : ℚ)⁻¹^2)
    (by positivity) hζ (by positivity) (I.midpoint+θ)⁻¹
    (muH D (inverse_length_le_1024 hL)+(θ : ℝ)) hv
  have hcal : |(((I.midpoint+θ)⁻¹ : ℚ) : ℝ)⁻¹-
      (muH D (inverse_length_le_1024 hL)+(θ : ℝ))| ≤ (ζ : ℝ)^2/2 := by
    rw [Rat.cast_inv, inv_inv, Rat.cast_add, add_sub_add_right_eq_sub]
    exact herr.trans (by nlinarith only [sq_nonneg (ζ : ℝ)])
  refine ⟨hround.1, ?_, htune hcal⟩
  have he := (abs_le.mp hround.2.1).2
  have hbase : (2 : ℚ)^129+(2 : ℚ)^128 ≤ (2 : ℚ)^130 := by norm_num
  have hnorm := mul_le_mul_of_nonneg_right hbase (sq_nonneg (L : ℚ)⁻¹)
  have hout : (onsiteRound L hLN ζ hζ I θ).value ≤ (2 : ℚ)^130*(L : ℚ)⁻¹^2 := by
    change (onsiteRound L hLN ζ hζ I θ).value-(I.midpoint+θ)⁻¹ ≤ _ at he
    nlinarith only [he, hvhi, hnorm]
  have hr : ((onsiteRound L hLN ζ hζ I θ).value : ℝ) ≤
      (((2 : ℚ)^130*(L : ℚ)⁻¹^2 : ℚ) : ℝ) := Rat.cast_le.mpr hout
  push_cast at hr
  exact hr

#print axioms couplingRound_error
#print axioms onsiteRound_bounds

end Maxwell.Continuum.FiniteAuxiliary
