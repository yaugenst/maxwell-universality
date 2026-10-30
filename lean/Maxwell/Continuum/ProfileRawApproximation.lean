import Maxwell.Continuum.ProfileFiniteSeries
import Maxwell.Continuum.ProfileRoundedCoefficients

/-! Uniform value and derivative accuracy for the explicit finite rounded profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set

def rawProfile (N : ℕ) : ℝ → ℝ :=
  finiteProfile (profileDegree N) (fun j => ((roundedCoefficient N j).value : ℝ))

def rawProfileDerivative (N : ℕ) : ℝ → ℝ :=
  finiteProfileDerivative (profileDegree N) (fun j => ((roundedCoefficient N j).value : ℝ))

theorem rawProfile_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (rawProfile N) (rawProfileDerivative N t) t := finiteProfile_hasDerivAt _ _ _

theorem rawProfile_contDiff (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawProfile N) :=
  finiteProfile_contDiff _ _

theorem profileDegree_truncation (N : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |radial t-exactTruncation (profileDegree N) t| ≤ (1/2 : ℝ)^(N+100) ∧
    |deriv radial t-exactTruncationDerivative (profileDegree N) t| ≤ (1/2 : ℝ)^(N+100) := by
  constructor
  · apply (exactTruncation_error (profileDegree N) ht).trans
    apply le_trans _ (profileDegree_precision N)
    gcongr <;> norm_num
  · apply (exactTruncation_derivative_error (profileDegree N) ht).trans
    apply le_trans _ (profileDegree_precision N)
    gcongr <;> norm_num

theorem rawProfile_errors (N : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |radial t-rawProfile N t| ≤ (1/2 : ℝ)^(N+26) ∧
    |deriv radial t-rawProfileDerivative N t| ≤ (1/2 : ℝ)^(N+26) := by
  have hη : 0 ≤ 9*(1/2 : ℝ)^profileWorkBits N := by positivity
  have hc (j : ℕ) (hj : j < profileDegree N) := roundedCoefficient_error N j hj.le
  have hfv := finiteProfile_coefficient_error (profileDegree N) cosineCoefficient
    (fun j => ((roundedCoefficient N j).value : ℝ)) hη hc ht
  have hfd := finiteProfile_derivative_coefficient_error (profileDegree N) cosineCoefficient
    (fun j => ((roundedCoefficient N j).value : ℝ)) hη hc ht
  change |exactTruncation (profileDegree N) t-rawProfile N t| ≤ _ at hfv
  change |exactTruncationDerivative (profileDegree N) t-rawProfileDerivative N t| ≤ _ at hfd
  have hb := profileWorkBits_error N
  have hD : 0 ≤ (profileDegree N : ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ (1/2 : ℝ)^profileWorkBits N := by positivity
  have hpoly : (profileDegree N : ℝ) ≤ 2*((profileDegree N : ℝ)+1)^3 := by
    have h := le_self_pow₀ (by linarith : (1 : ℝ) ≤ (profileDegree N : ℝ)+1)
      (by decide : (3 : ℕ) ≠ 0)
    linarith
  have hval : (profileDegree N : ℝ)*(9*(1/2 : ℝ)^profileWorkBits N) ≤ (1/2 : ℝ)^(N+27) := by
    apply le_trans _ hb
    nlinarith only [mul_le_mul_of_nonneg_right hpoly hp]
  have hder : 2*(profileDegree N : ℝ)^3*(9*(1/2 : ℝ)^profileWorkBits N) ≤
      (1/2 : ℝ)^(N+27) := by
    apply le_trans _ hb
    have hh : (profileDegree N : ℝ)^3 ≤ ((profileDegree N : ℝ)+1)^3 := by gcongr; linarith
    nlinarith only [mul_le_mul_of_nonneg_right hh hp]
  have htr := profileDegree_truncation N ht
  have hsmall : (1/2 : ℝ)^(N+100) ≤ (1/2 : ℝ)^(N+27) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he : 2*(1/2 : ℝ)^(N+27)=(1/2 : ℝ)^(N+26) := by
    rw [show N+27=(N+26)+1 by omega, pow_succ]
    ring
  constructor
  · calc
      _ ≤ |radial t-exactTruncation (profileDegree N) t|+
        |exactTruncation (profileDegree N) t-rawProfile N t| := abs_sub_le _ _ _
      _ ≤ 2*(1/2 : ℝ)^(N+27) := by linarith
      _ = _ := he
  · calc
      _ ≤ |deriv radial t-exactTruncationDerivative (profileDegree N) t|+
        |exactTruncationDerivative (profileDegree N) t-rawProfileDerivative N t| := abs_sub_le _ _ _
      _ ≤ 2*(1/2 : ℝ)^(N+27) := by linarith
      _ = _ := he

#print axioms rawProfile_errors

end Maxwell.Continuum.Profile
