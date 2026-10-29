import Maxwell.Realization.Parameters
import Mathlib.Data.Nat.Log

/-! Integer resource exponents for the selected geometric scales.
All fixed constants are obtained by rational comparisons and integer powers;
no transcendental constant is evaluated by the construction. -/
namespace Maxwell.Realization

/-- A certified power-of-two inverse budget bounds the least selected precision. -/
theorem precisionBits_le_of_inverse_le_pow (budget : ℚ) (hbudget : 0 < budget)
    (bits : ℕ) (hbound : budget⁻¹ ≤ (2:ℚ)^bits) : precisionBits budget hbudget ≤ bits := by
  apply Nat.find_min'
  apply le_min (pow_le_one₀ (by norm_num) (by norm_num))
  have h := mul_le_mul_of_nonneg_left hbound hbudget.le
  rw [mul_inv_cancel₀ (ne_of_gt hbudget)] at h
  rw [div_pow, one_pow]
  exact (div_le_iff₀ (by positivity : (0:ℚ)<2^bits)).mpr (by nlinarith)

/-- Polynomial inverse budgets yield a literal natural-bit bound. -/
theorem precisionBits_le_clog (budget : ℚ) (hbudget : 0 < budget)
    (m c e : ℕ) (hbound : budget⁻¹ ≤ (2:ℚ)^c*(m:ℚ)^e) :
    precisionBits budget hbudget ≤ c+e*Nat.clog 2 m := by
  apply precisionBits_le_of_inverse_le_pow budget hbudget
  have hm : (m:ℚ)≤(2:ℚ)^(Nat.clog 2 m) := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) m
  calc
    _ ≤ (2:ℚ)^c*(m:ℚ)^e := hbound
    _ ≤ (2:ℚ)^c*((2:ℚ)^Nat.clog 2 m)^e := by gcongr
    _ = _ := by rw [pow_add]; congr 1; rw [← pow_mul, Nat.mul_comm]

/-- The least power of two above a positive integer is at most twice it. -/
theorem two_pow_clog_le_twice (m : ℕ) (hm : 0 < m) : 2^Nat.clog 2 m ≤ 2*m := by
  cases hk : Nat.clog 2 m with
  | zero => simp only [pow_zero]; omega
  | succ k =>
    have hp : 2^k < m := (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mp (by omega)
    rw [pow_succ]
    omega

namespace SpacingPlatform

def ratioHalfSteps (P : SpacingPlatform) : ℕ :=
  geometricSteps P.ratio (1/2) P.ratio_pos P.ratio_lt_one (by norm_num)

/-- One fixed block of ratio steps shrinks by at least one binary digit. -/
theorem spacing_le_binary (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    P.spacing K ε hK hε ≤ P.fixedFloor + P.ratioHalfSteps *
      precisionBits (ε/(P.weight*K)) (div_pos hε (mul_pos P.weight_pos hK)) := by
  let b := precisionBits (ε/(P.weight*K)) (div_pos hε (mul_pos P.weight_pos hK))
  have hp : P.ratio^(P.ratioHalfSteps*b) ≤ ε/(P.weight*K) := by
    rw [pow_mul]
    calc
      _ ≤ (1/2:ℚ)^b := pow_le_pow_left₀ (pow_nonneg P.ratio_pos.le _)
        (geometricSteps_spec P.ratio (1/2) P.ratio_pos P.ratio_lt_one (by norm_num)) b
      _ ≤ _ := (geometricSteps_spec (1/2) (precisionBudget (ε/(P.weight*K)))
        (by norm_num) (by norm_num) (precisionBudget_pos _ (div_pos hε (mul_pos P.weight_pos hK)))).trans
          (min_le_right _ _)
  have hn : geometricSteps P.ratio (ε/(P.weight*K)) P.ratio_pos P.ratio_lt_one
      (div_pos hε (mul_pos P.weight_pos hK)) ≤ P.ratioHalfSteps*b := Nat.find_min' _ hp
  dsimp [b] at hn
  unfold spacing
  exact max_le (by omega) (by omega)

/-- Fully natural logarithmic separation from a polynomial reciprocal
logical error budget. -/
theorem spacing_le_clog (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε)
    (m c e : ℕ) (hbound : (ε/(P.weight*K))⁻¹ ≤ (2:ℚ)^c*(m:ℚ)^e) :
    P.spacing K ε hK hε ≤ (P.fixedFloor+P.ratioHalfSteps*c) +
      (P.ratioHalfSteps*e)*Nat.clog 2 m := by
  have hp := precisionBits_le_clog (ε/(P.weight*K)) (div_pos hε (mul_pos P.weight_pos hK)) m c e hbound
  have h := (P.spacing_le_binary K ε hK hε).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left P.ratioHalfSteps hp) P.fixedFloor)
  convert h using 1
  ring

end SpacingPlatform

/-- A rational geometric base admits an explicit integer reciprocal bound. -/
theorem geometric_inverse_integer_bound (r : ℚ) (hr : 0 < r) (m d d₀ d₁ : ℕ)
    (hm : 0 < m) (hd : d ≤ d₀+d₁*Nat.clog 2 m) :
    (r^d)⁻¹ ≤ (2:ℚ)^(precisionBits r hr*(d₀+d₁)) *
      (m:ℚ)^(precisionBits r hr*d₁) := by
  let R := precisionBits r hr
  have hrinv : r⁻¹ ≤ (2:ℚ)^R := by
    have h := precisionUnit_le r hr
    change (1:ℚ)/2^R ≤ r at h
    have hm := (div_le_iff₀ (by positivity : (0:ℚ)<2^R)).mp h
    exact (inv_le_iff_one_le_mul₀ hr).mpr (by nlinarith)
  have hm' : (2:ℚ)^Nat.clog 2 m ≤ 2*(m:ℚ) := by exact_mod_cast two_pow_clog_le_twice m hm
  calc
    _ = (r⁻¹)^d := (inv_pow _ _).symm
    _ ≤ ((2:ℚ)^R)^d := pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hrinv d
    _ = (2:ℚ)^(R*d) := (pow_mul _ _ _).symm
    _ ≤ (2:ℚ)^(R*(d₀+d₁*Nat.clog 2 m)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left R hd)
    _ = (2:ℚ)^(R*d₀)*((2:ℚ)^Nat.clog 2 m)^(R*d₁) := by
      rw [Nat.mul_add, pow_add]
      congr 1
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (2:ℚ)^(R*d₀)*(2*(m:ℚ))^(R*d₁) := by gcongr
    _ = _ := by rw [mul_pow, Nat.mul_add, pow_add]; ring

/-- For m≥2, the fixed power-of-two coefficient is absorbed into an explicit
natural exponent, valid even for the smallest non-base input. -/
theorem geometric_inverse_literal (r : ℚ) (hr : 0 < r) (m d d₀ d₁ : ℕ)
    (hm : 2 ≤ m) (hd : d ≤ d₀+d₁*Nat.clog 2 m) :
    (r^d)⁻¹ ≤ (m:ℚ)^(precisionBits r hr*(d₀+2*d₁)) := by
  have h := geometric_inverse_integer_bound r hr m d d₀ d₁ (by omega) hd
  apply h.trans
  calc
    _ ≤ (m:ℚ)^(precisionBits r hr*(d₀+d₁))*(m:ℚ)^(precisionBits r hr*d₁) := by
      gcongr
      exact_mod_cast hm
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- The fixed reciprocal of a positive rational has an effectively selected
binary exponent. -/
theorem inverse_le_two_pow_precision (x : ℚ) (hx : 0 < x) :
    x⁻¹ ≤ (2:ℚ)^precisionBits x hx := by
  have h := precisionUnit_le x hx
  change (1:ℚ)/2^precisionBits x hx ≤ x at h
  have hh := (div_le_iff₀ (by positivity : (0:ℚ)<2^precisionBits x hx)).mp h
  exact (inv_le_iff_one_le_mul₀ hx).mpr (by nlinarith)

theorem inverse_le_input_pow (x : ℚ) (hx : 0 < x) (m : ℕ) (hm : 2 ≤ m) :
    x⁻¹ ≤ (m:ℚ)^precisionBits x hx :=
  (inverse_le_two_pow_precision x hx).trans (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _)

namespace SpacingPlatform

def spacingBase (P : SpacingPlatform) (c : ℕ) : ℕ := P.fixedFloor+P.ratioHalfSteps*c

def spacingSlope (P : SpacingPlatform) (e : ℕ) : ℕ := P.ratioHalfSteps*e

def zetaExponent (P : SpacingPlatform) (c e : ℕ) : ℕ :=
  precisionBits P.r P.r_pos*(P.spacingBase c+2*P.spacingSlope e)

def alphaExponent (P : SpacingPlatform) (c e : ℕ) : ℕ :=
  precisionBits (P.c/4) (by exact div_pos P.c_pos (by norm_num)) +
    precisionBits P.a P.a_pos*(P.spacingBase c+2*P.spacingSlope e)

/-- The actual selected geometric scales meet literal input powers with
computable natural exponents, for every m≥2. -/
theorem selected_scales_literal (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε)
    (m c e : ℕ) (hm : 2 ≤ m) (hbound : (ε/(P.weight*K))⁻¹ ≤ (2:ℚ)^c*(m:ℚ)^e) :
    (P.zeta (P.spacing K ε hK hε))⁻¹ ≤ (m:ℚ)^(P.zetaExponent c e) ∧
      (P.alpha (P.spacing K ε hK hε))⁻¹ ≤ (m:ℚ)^(P.alphaExponent c e) := by
  have hd := P.spacing_le_clog K ε hK hε m c e hbound
  refine ⟨geometric_inverse_literal P.r P.r_pos m _ _ _ hm hd, ?_⟩
  have ha := geometric_inverse_literal P.a P.a_pos m _ _ _ hm hd
  have hc := inverse_le_input_pow (P.c/4) (div_pos P.c_pos (by norm_num)) m hm
  have h := mul_le_mul hc ha (inv_nonneg.mpr (pow_nonneg P.a_pos.le _)) (by positivity)
  unfold alpha alphaExponent spacingBase spacingSlope
  rw [mul_inv_rev, pow_add, mul_comm ((P.a ^ P.spacing K ε hK hε)⁻¹) ((P.c/4)⁻¹)]
  exact h

end SpacingPlatform

/-- Minimal dyadic selection preserves a literal inverse-polynomial budget
with one extra natural exponent, including budgets larger than one. -/
theorem precisionUnit_inverse_literal (budget : ℚ) (hbudget : 0 < budget)
    (m e : ℕ) (hm : 2 ≤ m) (hbound : budget⁻¹ ≤ (m:ℚ)^e) :
    (precisionUnit budget hbudget)⁻¹ ≤ (m:ℚ)^(e+1) := by
  have hcap : (precisionBudget budget)⁻¹ ≤ (m:ℚ)^e := by
    by_cases hb : budget≤1
    · simpa only [precisionBudget, min_eq_right hb] using hbound
    · rw [precisionBudget, min_eq_left (le_of_not_ge hb), inv_one]
      exact one_le_pow₀ (by exact_mod_cast (show 1≤m by omega))
  calc
    _ ≤ 2*(precisionBudget budget)⁻¹ := (precisionUnit_inverse budget hbudget).le
    _ ≤ 2*(m:ℚ)^e := mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ ≤ (m:ℚ)*(m:ℚ)^e := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
    _ = _ := by rw [pow_succ]; ring

namespace PhysicalConstants

def detuningExponent (P : PhysicalConstants) (zetaExponent : ℕ) : ℕ :=
  precisionBits P.detuningLower P.detuningLower_pos + 2*zetaExponent

/-- The actual chosen detuning interval remains inverse polynomial with
an explicit natural exponent. -/
theorem detuningWidth_inverse_literal (P : PhysicalConstants) (ζ : ℚ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (m e : ℕ) (hm : 2 ≤ m)
    (hbound : ζ⁻¹ ≤ (m:ℚ)^e) :
    (P.detuningWidth ζ hζ)⁻¹ ≤ (m:ℚ)^(P.detuningExponent e) := by
  have hl := P.detuningWidth_lower ζ hζ hζ1
  have hpos : 0 < P.detuningLower*ζ^2 := mul_pos P.detuningLower_pos (pow_pos hζ _)
  have hi := (inv_le_inv₀ (P.detuningWidth_pos ζ hζ) hpos).mpr hl.le
  have hc := inverse_le_input_pow P.detuningLower P.detuningLower_pos m hm
  calc
    _ ≤ (P.detuningLower*ζ^2)⁻¹ := hi
    _ = P.detuningLower⁻¹*(ζ⁻¹)^2 := by rw [mul_inv_rev, inv_pow]; ring
    _ ≤ (m:ℚ)^precisionBits P.detuningLower P.detuningLower_pos * ((m:ℚ)^e)^2 :=
      mul_le_mul hc (pow_le_pow_left₀ (inv_nonneg.mpr hζ.le) hbound 2) (by positivity) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]; unfold detuningExponent; congr 1; omega

end PhysicalConstants

end Maxwell.Realization
