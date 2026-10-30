import Maxwell.Continuum.ParameterSpacingSearch

/-! Exact binary bounds for the rational scales used by the encoder. -/

namespace Maxwell.Continuum.Parameters

set_option exponentiation.threshold 2048

 theorem binary_mul {x y : ℚ} {a b : ℕ} (hx : x ≤ (2 : ℚ)^a)
    (hy : y ≤ (2 : ℚ)^b) (hy0 : 0 ≤ y) : x*y ≤ (2 : ℚ)^(a+b) := by
  rw [pow_add]
  exact mul_le_mul hx hy hy0 (by positivity)

 theorem binary_add {x y : ℚ} {a b : ℕ} (hx : x ≤ (2 : ℚ)^a)
    (hy : y ≤ (2 : ℚ)^b) : x+y ≤ (2 : ℚ)^(a+b+1) := by
  have hx' := hx.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right a b))
  have hy' := hy.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left b a))
  rw [pow_succ]
  linarith

 theorem binary_one_add {x : ℚ} {a : ℕ} (hx : x ≤ (2 : ℚ)^a) :
    1+x ≤ (2 : ℚ)^(a+1) := by
  have h1 : (1 : ℚ) ≤ 2^a := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

 theorem binary_pow {x : ℚ} {a : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ (2 : ℚ)^a) (k : ℕ) :
    x^k ≤ (2 : ℚ)^(a*k) := by rw [pow_mul]; exact pow_le_pow_left₀ hx0 hx k

 theorem alpha_inverse_formula (L d : ℕ) :
    (alpha L d)⁻¹ = (2 : ℚ)^1026*(L : ℚ)⁻¹^2*(8 : ℚ)^d := by
  simp only [alpha, mul_inv_rev, inv_inv, ← inv_pow]
  rw [show (1/8 : ℚ)⁻¹ = 8 by norm_num]
  ring

 theorem alpha_inverse_binary {L : ℕ} (hL : 0 < L) (d : ℕ) :
    (alpha L d)⁻¹ ≤ (2 : ℚ)^(1026+3*d) := by
  have hL1 : (1 : ℚ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hi : (L : ℚ)⁻¹^2 ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr (Nat.cast_nonneg L)) (inv_le_one_of_one_le₀ hL1)
  rw [alpha_inverse_formula]
  calc
    _ ≤ (2 : ℚ)^1026*1*(8 : ℚ)^d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by positivity)) (by positivity)
    _ = _ := by rw [mul_one, show (8 : ℚ) = 2^3 by norm_num, ← pow_mul, ← pow_add]

 theorem tau_inverse_binary {L a : ℕ} (hL : 0 < L) (hLa : L ≤ 2^a) (d : ℕ) :
    (tau L d hL)⁻¹ ≤ (2 : ℚ)^(25+4*a+4*d) := by
  have hLa' : (L : ℚ) ≤ (2 : ℚ)^a := by exact_mod_cast hLa
  have h3 : (3 : ℚ)^(2*d) ≤ (2 : ℚ)^(4*d) := by
    calc
      _ ≤ (4 : ℚ)^(2*d) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by rw [show (4 : ℚ) = 2^2 by norm_num, ← pow_mul]; congr 1; omega
  apply (tau_inverse_bound L d hL).le.trans
  have h4 := binary_pow (Nat.cast_nonneg L) hLa' 4
  have hb := binary_mul (binary_mul (le_refl ((2 : ℚ)^25)) h4 (by positivity)) h3 (by positivity)
  simpa only [Nat.mul_comm a 4, Nat.add_assoc] using hb

 theorem precisionBits_le_of_binary {ε : ℚ} (hε : 0 < ε) {c : ℕ}
    (hc : (1/2 : ℚ)^c ≤ ε) : Realization.precisionBits ε hε ≤ c := by
  unfold Realization.precisionBits Realization.geometricSteps
  apply Nat.find_min'
  exact le_min (pow_le_one₀ (by norm_num) (by norm_num)) hc

 theorem rationalUpperBits_le {x : ℚ} {a : ℕ} (hx : x ≤ (2 : ℚ)^a) :
    rationalUpperBits x ≤ a := by
  apply Nat.clog_le_of_le_pow
  apply (Nat.ceil_le).mpr
  exact_mod_cast hx

#print axioms alpha_inverse_binary
#print axioms tau_inverse_binary

end Maxwell.Continuum.Parameters
