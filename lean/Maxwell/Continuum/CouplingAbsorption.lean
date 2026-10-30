import Maxwell.Continuum.MasterConstants
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Symbolic absorption of the continuum interaction errors under the
literal spacing and tail hypotheses in the manuscript. No large integer
array or master-constant power is evaluated. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.MasterConstants

attribute [local irreducible] Cs

theorem spacing_ge_one {d : ℝ} (hd : ds ≤ d) : 1 ≤ d :=
  (one_le_pow₀ Cs_ge_one).trans hd

theorem spacing_pos {d : ℝ} (hd : ds ≤ d) : 0 < d :=
  lt_of_lt_of_le (by norm_num) (spacing_ge_one hd)

theorem spacing_sqrt_lower {d : ℝ} (hd : ds ≤ d) : Cs^4 ≤ Real.sqrt d := by
  apply Real.le_sqrt_of_sq_le
  change Cs^8 ≤ d at hd
  simpa only [← pow_mul, show 4*2 = 8 by omega] using hd

theorem master_cubic_ratio_small : Cs/Cs^4 ≤ (1/(2 : ℝ)^512)/8 := by
  have hc : (2 : ℝ)^1024 ≤ Cs := fixed_power_le_Cs (by norm_num [exponent])
  have hp : (2 : ℝ)^512*8 ≤ Cs^3 :=
    (by norm_num : (2 : ℝ)^512*8 ≤ ((2 : ℝ)^1024)^3).trans
      (pow_le_pow_left₀ (by positivity) hc 3)
  rw [div_div]
  apply (div_le_div_iff₀ (pow_pos Cs_pos 4) (by positivity : 0 < (2 : ℝ)^512*8)).mpr
  simp only [one_mul]
  calc
    Cs*((2 : ℝ)^512*8) ≤ Cs*Cs^3 := mul_le_mul_of_nonneg_left hp Cs_pos.le
    _ = Cs^4 := by ring

theorem local_error_ratio {d b : ℝ} (hd : ds ≤ d) (hb : 1/(2 : ℝ)^512 ≤ b) :
    Cs/Real.sqrt d ≤ b/8 :=
  (div_le_div_of_nonneg_left Cs_pos.le (pow_pos Cs_pos 4) (spacing_sqrt_lower hd)).trans
    (master_cubic_ratio_small.trans (div_le_div_of_nonneg_right hb (by norm_num)))

theorem regular_error_ratio {L d b : ℝ} (hd : ds ≤ d)
    (hspace : Cs^4*L ≤ d^15) (hb : 1/(2 : ℝ)^512 ≤ b) :
    Cs*L/d^15 ≤ b/8 := by
  have hr : Cs*L/d^15 ≤ Cs/Cs^4 := by
    apply (div_le_div_iff₀ (pow_pos (spacing_pos hd) 15) (pow_pos Cs_pos 4)).mpr
    calc
      Cs*L*Cs^4 = Cs*(Cs^4*L) := by ring
      _ ≤ Cs*d^15 := mul_le_mul_of_nonneg_left hspace Cs_pos.le
  exact hr.trans (master_cubic_ratio_small.trans (div_le_div_of_nonneg_right hb (by norm_num)))

theorem analytic_errors_le_quarter {L d b I : ℝ} (hd : ds ≤ d)
    (hspace : Cs^4*L ≤ d^15) (hb : 1/(2 : ℝ)^512 ≤ b) :
    Cs*L^2*Real.exp (-I*d)/(d*Real.sqrt d) + Cs*L^3*Real.exp (-I*d)/d^16 ≤
      (L^2*Real.exp (-I*d)*b/d)/4 := by
  have hd0 := spacing_pos hd
  have hs0 := Real.sqrt_pos.mpr hd0
  have hp : 0 ≤ L^2*Real.exp (-I*d)/d := by positivity
  have hl : Cs*L^2*Real.exp (-I*d)/(d*Real.sqrt d) ≤
      (L^2*Real.exp (-I*d)*b/d)/8 := by
    calc
      _ = (L^2*Real.exp (-I*d)/d)*(Cs/Real.sqrt d) := by field_simp
      _ ≤ (L^2*Real.exp (-I*d)/d)*(b/8) :=
        mul_le_mul_of_nonneg_left (local_error_ratio hd hb) hp
      _ = _ := by ring
  have hr : Cs*L^3*Real.exp (-I*d)/d^16 ≤
      (L^2*Real.exp (-I*d)*b/d)/8 := by
    calc
      _ = (L^2*Real.exp (-I*d)/d)*(Cs*L/d^15) := by
        rw [show 16 = 15+1 by omega, pow_succ]
        field_simp
      _ ≤ (L^2*Real.exp (-I*d)/d)*(b/8) :=
        mul_le_mul_of_nonneg_left (regular_error_ratio hd hspace hb) hp
      _ = _ := by ring
  linarith only [hl, hr]

theorem exponential_spacing_margin {d : ℝ} (hd : ds ≤ d) :
    (2 : ℝ)^1024*d ≤ Real.exp (d/50) := by
  have hd0 := spacing_pos hd
  have hc : (2 : ℝ)^2048 ≤ Cs := fixed_power_le_Cs (by norm_num [exponent])
  have hcp : Cs ≤ Cs^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ Cs_ge_one (by omega : 1 ≤ 8)
  have hlarge : 5000*(2 : ℝ)^1024 ≤ d :=
    (by norm_num : 5000*(2 : ℝ)^1024 ≤ (2 : ℝ)^2048).trans (hc.trans (hcp.trans hd))
  have he := Real.pow_div_factorial_le_exp (d/50) (by positivity) 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at he
  have hm := mul_le_mul_of_nonneg_right hlarge hd0.le
  have hp : (2 : ℝ)^1024*d ≤ (d/50)^2/2 := by nlinarith only [hm]
  exact hp.trans he

theorem exponential_spacing_margin_div {d : ℝ} (hd : ds ≤ d) :
    (2 : ℝ)^1024 ≤ Real.exp (d/50)/d :=
  (le_div_iff₀ (spacing_pos hd)).mpr (exponential_spacing_margin hd)

theorem leading_term_lower {L d b I : ℝ} (hd : ds ≤ d)
    (hb : 1/(2 : ℝ)^512 ≤ b) (hI : I ≤ Real.log 8-1/50) :
    2*(cu*L^2*Real.exp (-Real.log 8*d)) ≤ L^2*Real.exp (-I*d)*b/d := by
  have hd0 := spacing_pos hd
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have he : Real.exp (-Real.log 8*d)*Real.exp (d/50) ≤ Real.exp (-I*d) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hI hd0.le
    nlinarith only [hm]
  have hm : Real.exp (-Real.log 8*d)*((2 : ℝ)^1024*d) ≤ Real.exp (-I*d) :=
    (mul_le_mul_of_nonneg_left (exponential_spacing_margin hd) (Real.exp_pos _).le).trans he
  have hc : 2*cu ≤ (2 : ℝ)^1024*b :=
    (by norm_num [cu] : 2*cu ≤ (2 : ℝ)^1024*(1/(2 : ℝ)^512)).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  calc
    _ = (L^2*Real.exp (-Real.log 8*d))*(2*cu) := by ring
    _ ≤ (L^2*Real.exp (-Real.log 8*d))*((2 : ℝ)^1024*b) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (L^2*b)*(Real.exp (-Real.log 8*d)*((2 : ℝ)^1024*d))/d := by field_simp
    _ ≤ (L^2*b)*Real.exp (-I*d)/d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) hd0.le
    _ = _ := by ring

theorem coupling_lower_of_green_remainder {L d b I : ℝ} {J : ℂ}
    (hd : ds ≤ d) (hspace : Cs^4*L ≤ d^15) (hb : 1/(2 : ℝ)^512 ≤ b)
    (hI : I ≤ Real.log 8-1/50)
    (htail : Cs*L^5*Real.exp (-cs*L) ≤ (cu/4)*L^2*Real.exp (-Real.log 8*d))
    (herr : ‖J-((L^2*Real.exp (-I*d)*b/d : ℝ) : ℂ)‖ ≤
      Cs*L^2*Real.exp (-I*d)/(d*Real.sqrt d) + Cs*L^3*Real.exp (-I*d)/d^16 +
        Cs*L^5*Real.exp (-cs*L)) :
    cu*L^2*Real.exp (-Real.log 8*d) ≤ J.re := by
  have hs := analytic_errors_le_quarter (I := I) hd hspace hb
  have hm := leading_term_lower (L := L) hd hb hI
  have hr : L^2*Real.exp (-I*d)*b/d-J.re ≤ ‖J-((L^2*Real.exp (-I*d)*b/d : ℝ) : ℂ)‖ := by
    have he := Complex.re_le_norm (((L^2*Real.exp (-I*d)*b/d : ℝ) : ℂ)-J)
    simpa only [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] using he
  have he := hr.trans herr
  have ht0 : 0 ≤ cu*L^2*Real.exp (-Real.log 8*d) := by unfold cu; positivity
  have ht : Cs*L^5*Real.exp (-cs*L) ≤ (cu*L^2*Real.exp (-Real.log 8*d))/4 :=
    htail.trans_eq (by ring)
  linarith only [he, hs, hm, ht, ht0]

theorem explicit_errors_le_master {L d I : ℝ} (hL : Ls ≤ L) (hd : ds ≤ d) :
    (2 : ℝ)^70069*L^2*Real.exp (-I*d)/(d*Real.sqrt d) +
        2*((2 : ℝ)^220000*L^3*Real.exp (-I*d)/d^16) +
        (2 : ℝ)^341*L^3*Real.exp (-cs*L) ≤
      Cs*L^2*Real.exp (-I*d)/(d*Real.sqrt d) + Cs*L^3*Real.exp (-I*d)/d^16 +
        Cs*L^5*Real.exp (-cs*L) := by
  have hd0 := spacing_pos hd
  have hL0 := length_pos hL
  apply add_le_add
  · apply add_le_add
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (fixed_power_le_Cs (by norm_num [exponent])) (sq_nonneg L))
        (Real.exp_pos _).le
    · have hc : 2*(2 : ℝ)^220000 ≤ Cs := by
        rw [← pow_succ']
        exact fixed_power_le_Cs (by norm_num [exponent])
      calc
        _ = (2*(2 : ℝ)^220000)*L^3*Real.exp (-I*d)/d^16 := by
          have he (a b c e : ℝ) : 2*(a*b*c/e) = (2*a)*b*c/e := by ring
          exact he _ _ _ _
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (pow_nonneg hL0.le 3)) (Real.exp_pos _).le)
          (pow_nonneg hd0.le 16)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul (fixed_power_le_Cs (by norm_num [exponent]))
        (pow_le_pow_right₀ (length_ge_one hL) (by omega : 3 ≤ 5))
        (pow_nonneg hL0.le 3) Cs_pos.le) (Real.exp_pos _).le

theorem coupling_lower_of_explicit_remainder {L d b I : ℝ} {J : ℂ}
    (hL : Ls ≤ L) (hd : ds ≤ d) (hspace : Cs^4*L ≤ d^15)
    (hb : 1/(2 : ℝ)^512 ≤ b) (hI : I ≤ Real.log 8-1/50)
    (htail : Cs*L^5*Real.exp (-cs*L) ≤ (cu/4)*L^2*Real.exp (-Real.log 8*d))
    (herr : ‖J-((L^2*Real.exp (-I*d)*b/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*L^2*Real.exp (-I*d)/(d*Real.sqrt d) +
        2*((2 : ℝ)^220000*L^3*Real.exp (-I*d)/d^16) +
        (2 : ℝ)^341*L^3*Real.exp (-cs*L)) :
    cu*L^2*Real.exp (-Real.log 8*d) ≤ J.re :=
  coupling_lower_of_green_remainder hd hspace hb hI htail
    (herr.trans (explicit_errors_le_master hL hd))

#print axioms coupling_lower_of_explicit_remainder

end Maxwell.Continuum.MasterConstants
