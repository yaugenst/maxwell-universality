import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! An explicit logarithmic buffer for polynomial volume feedback. -/

namespace Maxwell.Realization.Buffer

noncomputable section

/-- The dimension feedback separates into an input-size factor and a buffer
factor; this is the actual cubic volume law rather than a fixed-volume model. -/
theorem volume_factor (m s b : ℕ) (N C : ℝ) (hN0 : 0 ≤ N) (hC : 0 ≤ C)
    (hN : N ≤ C * ((s : ℝ) + b + 1)^3) :
    ((m : ℝ) + N)^2 ≤
      ((m : ℝ) + 1)^2 * (C + 1)^2 * ((s : ℝ) + 1)^6 * ((b : ℝ) + 1)^6 := by
  have hbase : (s : ℝ) + b + 1 ≤ ((s : ℝ) + 1) * ((b : ℝ) + 1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
      (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s : ℝ) + b + 1) hbase 3
  have hvol : (N : ℝ) ≤ C * (((s : ℝ) + 1)^3 * ((b : ℝ) + 1)^3) := by
    calc
      _ ≤ C * ((s : ℝ) + b + 1)^3 := hN
      _ ≤ C * (((s : ℝ) + 1) * ((b : ℝ) + 1))^3 := mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by ring
  have hsb : 1 ≤ ((s : ℝ) + 1)^3 * ((b : ℝ) + 1)^3 := by
    have hs : 1 ≤ ((s : ℝ) + 1)^3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
    have hb : 1 ≤ ((b : ℝ) + 1)^3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])
    nlinarith
  have hlin : (m : ℝ) + N ≤
      ((m : ℝ) + 1) * (C + 1) * (((s : ℝ) + 1)^3 * ((b : ℝ) + 1)^3) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hC,
      mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
        (show 0 ≤ (C + 1) * (((s : ℝ) + 1)^3 * ((b : ℝ) + 1)^3) - 1 by nlinarith)]
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ) + N) hlin 2
  convert hh using 1; ring


/-- An explicit constant absorbs the degree-six buffer polynomial while preserving
half of its exponential decay rate. -/
lemma buffer_polynomial_six_bound (μ b : ℝ) (hμ : 0 < μ) (hb : 1 ≤ b) :
    (b + 1)^6 * Real.exp (-μ * b) ≤
      (46080 * (2 / μ)^6) * Real.exp (-(μ / 2) * b) := by
  have hb₀ : 0 ≤ b := by linarith
  have hpoly : (b + 1)^6 ≤ (2 * b)^6 := by gcongr; linarith
  have ht := Real.pow_div_factorial_le_exp (μ / 2 * b)
    (show 0 ≤ μ / 2 * b by positivity) 6
  norm_num at ht
  have hpow : (2 * b)^6 ≤ (46080 * (2 / μ)^6) * Real.exp (μ / 2 * b) := by
    calc
      _ = (46080 * (2 / μ)^6) * ((μ / 2 * b)^6 / 720) := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  calc
    _ ≤ ((46080 * (2 / μ)^6) * Real.exp (μ / 2 * b)) * Real.exp (-μ * b) :=
      mul_le_mul_of_nonneg_right (hpoly.trans hpow) (Real.exp_pos _).le
    _ = (46080 * (2 / μ)^6) * Real.exp (-(μ / 2) * b) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

lemma buffer_polynomial_six_constant_pos (μ : ℝ) (hμ : 0 < μ) :
    0 < 46080 * (2 / μ)^6 := by positivity

/-- A fixed positive constant, independent of logical size and requested error. -/
def fixedConstant (μ J g C : ℝ) : ℝ :=
  1 + 128 * (J + 1) / g * (C + 1)^2 * (46080 * (2 / μ)^6)

theorem fixedConstant_one_le (μ J g C : ℝ) (hJ : 0 ≤ J) (hg : 0 < g) :
    1 ≤ fixedConstant μ J g C := by
  unfold fixedConstant
  have h : 0 ≤ 128 * (J + 1) / g * (C + 1)^2 * (46080 * (2 / μ)^6) := by positivity
  linarith

/-- All varying quantities occur inside this logarithm. -/
def logarithmArgument (μ J g C : ℝ) (m s : ℕ) (τ ζ : ℝ) : ℝ :=
  fixedConstant μ J g C * ((m : ℝ) + 1)^2 * ((s : ℝ) + 1)^6 / (τ * ζ^2)

/-- Explicit finite buffer choice; the added unit supplies the polynomial
absorption theorem's lower bound. -/
def choice (μ J g C : ℝ) (m s : ℕ) (τ ζ : ℝ) : ℕ :=
  1 + ⌈(2 / μ) * Real.log (logarithmArgument μ J g C m s τ ζ)⌉₊

theorem choice_one_le (μ J g C : ℝ) (m s : ℕ) (τ ζ : ℝ) :
    1 ≤ choice μ J g C m s τ ζ := by unfold choice; omega

/-- Any buffer meeting the logarithmic exponential threshold controls the
actual cubic-volume feedback, uniformly in every permitted final dimension. -/
theorem feedback_volume_bound (μ J g C : ℝ) (hμ : 0 < μ) (hJ : 0 ≤ J)
    (hg : 0 < g) (hC : 0 ≤ C) (m s b : ℕ) (N : ℝ) (hN0 : 0 ≤ N) (hb : 1 ≤ b)
    (τ ζ : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ)
    (hN : (N : ℝ) ≤ C * ((s : ℝ) + b + 1)^3)
    (hexp : Real.exp (-(μ / 2) * b) ≤
      1 / logarithmArgument μ J g C m s τ ζ) :
    (4 * J / g) * (16 * ((m : ℝ) + N)^2 / τ) * Real.exp (-μ * b) ≤ ζ^2 / 2 := by
  let K := 46080 * (2 / μ)^6
  let V := ((m : ℝ) + 1)^2 * (C + 1)^2 * ((s : ℝ) + 1)^6
  have hK : 0 < K := by dsimp [K]; positivity
  have hF : 0 < fixedConstant μ J g C := lt_of_lt_of_le zero_lt_one
    (fixedConstant_one_le μ J g C hJ hg)
  have harg : 0 < logarithmArgument μ J g C m s τ ζ := by
    unfold logarithmArgument
    positivity
  have hpoly := buffer_polynomial_six_bound μ (b : ℝ) hμ (by exact_mod_cast hb)
  have hvol := volume_factor m s b N C hN0 hC hN
  have hcoef : 128 * J / g * (C + 1)^2 * K ≤ fixedConstant μ J g C := by
    calc
      _ ≤ 128 * (J + 1) / g * (C + 1)^2 * K := by gcongr; linarith
      _ ≤ fixedConstant μ J g C := by dsimp [fixedConstant, K]; linarith
  calc
    _ ≤ (64 * J / (g * τ)) * (V * ((b : ℝ) + 1)^6) * Real.exp (-μ * b) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hvol (show 0 ≤ 64 * J / (g * τ) by positivity))
        (Real.exp_pos (-μ * b)).le
      dsimp [V]
      convert hh using 1; ring
    _ = ((64 * J / (g * τ)) * V) * (((b : ℝ) + 1)^6 * Real.exp (-μ * b)) := by ring
    _ ≤ ((64 * J / (g * τ)) * V) * (K * Real.exp (-(μ / 2) * b)) :=
      mul_le_mul_of_nonneg_left hpoly (by dsimp [V]; positivity)
    _ ≤ ((64 * J / (g * τ)) * V) * (K / logarithmArgument μ J g C m s τ ζ) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hexp hK.le)
        (by dsimp [V]; positivity)
    _ = (128 * J / g * (C + 1)^2 * K / fixedConstant μ J g C) * (ζ^2 / 2) := by
      dsimp [V, logarithmArgument]
      field_simp
      ring
    _ ≤ ζ^2 / 2 := by
      have hh : 128 * J / g * (C + 1)^2 * K / fixedConstant μ J g C ≤ 1 :=
        (div_le_one hF).mpr hcoef
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ ζ^2 / 2)


private lemma buffer_logarithm_identity (m s : ℕ) (K τ ζ : ℝ)
    (hK : 1 ≤ K) (hτ : 0 < τ) (hζ : 0 < ζ) :
    Real.log (K * ((m : ℝ) + 1)^2 * ((s : ℝ) + 1)^6 / (τ * ζ^2)) =
      Real.log K + 2 * Real.log ((m : ℝ) + 1) +
        6 * Real.log ((s : ℝ) + 1) + Real.log (1 / τ) + 2 * Real.log (1 / ζ) := by
  have hK₀ : K ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul hK₀ (pow_ne_zero _ hm),
    Real.log_mul hτ.ne' (pow_ne_zero _ hζ.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow]
  simp only [one_div, Real.log_inv, Nat.cast_ofNat]
  ring

private lemma buffer_logarithm_argument_ge_one (m s : ℕ) (K τ ζ : ℝ)
    (hK : 1 ≤ K) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) :
    1 ≤ K * ((m : ℝ) + 1)^2 * ((s : ℝ) + 1)^6 / (τ * ζ^2) := by
  have hm : 1 ≤ ((m : ℝ) + 1)^2 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hs : 1 ≤ ((s : ℝ) + 1)^6 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) s])
  have hnum : 1 ≤ K * ((m : ℝ) + 1)^2 * ((s : ℝ) + 1)^6 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hm) hs
  have hζ₂ : ζ^2 ≤ 1 := by nlinarith
  have hden : τ * ζ^2 ≤ 1 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < τ * ζ^2)).mpr
  simpa only [one_mul] using hden.trans hnum

private lemma buffer_logarithm_ceil_bounds (μ A : ℝ) (hμ : 0 < μ) (hA : 1 ≤ A) :
    ((1 + Nat.ceil ((2 / μ) * Real.log A) : ℕ) : ℝ) ≤
      2 + (2 / μ) * Real.log A ∧
    Real.exp (-(μ / 2) * ((1 + Nat.ceil ((2 / μ) * Real.log A) : ℕ) : ℝ)) ≤ 1 / A := by
  have hq : 0 ≤ (2 / μ) * Real.log A := mul_nonneg (by positivity) (Real.log_nonneg hA)
  have hceil := Nat.ceil_lt_add_one hq
  have hle := Nat.le_ceil ((2 / μ) * Real.log A)
  constructor
  · push_cast
    linarith
  · have he : -(μ / 2) * ((1 + Nat.ceil ((2 / μ) * Real.log A) : ℕ) : ℝ) ≤
        -Real.log A := by
      have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ μ / 2 by positivity)
      have hc : (μ / 2) * ((2 / μ) * Real.log A) = Real.log A := by
        field_simp
      rw [hc] at hmul
      push_cast
      linarith
    calc
      _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr he
      _ = 1 / A := by rw [Real.exp_neg, Real.exp_log (lt_of_lt_of_le zero_lt_one hA), one_div]

theorem logarithmArgument_one_le (μ J g C : ℝ) (hJ : 0 ≤ J) (hg : 0 < g)
    (m s : ℕ) (τ ζ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    1 ≤ logarithmArgument μ J g C m s τ ζ :=
  buffer_logarithm_argument_ge_one m s (fixedConstant μ J g C) τ ζ
    (fixedConstant_one_le μ J g C hJ hg) hτ hτ1 hζ hζ1

/-- The chosen natural buffer has the required exponential suppression. -/
theorem choice_exponential_bound (μ J g C : ℝ) (hμ : 0 < μ) (hJ : 0 ≤ J) (hg : 0 < g)
    (m s : ℕ) (τ ζ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    Real.exp (-(μ / 2) * choice μ J g C m s τ ζ) ≤ 1 / logarithmArgument μ J g C m s τ ζ :=
  (buffer_logarithm_ceil_bounds μ _ hμ
    (logarithmArgument_one_le μ J g C hJ hg m s τ ζ hτ hτ1 hζ hζ1)).2

/-- Explicit logarithmic size bound, with every constant specified. -/
theorem choice_logarithmic_bound (μ J g C : ℝ) (hμ : 0 < μ) (hJ : 0 ≤ J) (hg : 0 < g)
    (m s : ℕ) (τ ζ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (choice μ J g C m s τ ζ : ℝ) ≤ 2 + (2 / μ) *
      (Real.log (fixedConstant μ J g C) + 2 * Real.log ((m : ℝ) + 1) +
       6 * Real.log ((s : ℝ) + 1) + Real.log (1 / τ) + 2 * Real.log (1 / ζ)) := by
  have h := (buffer_logarithm_ceil_bounds μ _ hμ
    (logarithmArgument_one_le μ J g C hJ hg m s τ ζ hτ hτ1 hζ hζ1)).1
  conv_rhs at h =>
    rw [logarithmArgument, buffer_logarithm_identity m s (fixedConstant μ J g C) τ ζ
      (fixedConstant_one_le μ J g C hJ hg) hτ hζ]
  exact h

/-- The explicit choice controls every actual dimension satisfying the cubic
geometric volume estimate. -/
theorem choice_feedback_bound (μ J g C : ℝ) (hμ : 0 < μ) (hJ : 0 ≤ J)
    (hg : 0 < g) (hC : 0 ≤ C) (m s N : ℕ)
    (τ ζ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hN : (N : ℝ) ≤ C * ((s : ℝ) + choice μ J g C m s τ ζ + 1)^3) :
    (4 * J / g) * (16 * ((m : ℝ) + N)^2 / τ) *
      Real.exp (-μ * choice μ J g C m s τ ζ) ≤ ζ^2 / 2 :=
  feedback_volume_bound μ J g C hμ hJ hg hC m s _ N (Nat.cast_nonneg _)
    (choice_one_le μ J g C m s τ ζ) τ ζ hτ hζ hN
    (choice_exponential_bound μ J g C hμ hJ hg m s τ ζ hτ hτ1 hζ hζ1)

/-- The precision inequality separately controls the spectral-shift term. -/
theorem shift_error_bound (g τ ζ : ℝ) (hg : 0 < g)
    (hτ : τ ≤ g^2 * ζ^2 / 16) : 2 * τ / g^2 ≤ ζ^2 / 8 := by
  apply (div_le_iff₀ (sq_pos_of_pos hg)).mpr
  nlinarith


private lemma buffer_geometric_decay_rate_pos (r : ℚ) (hr : 0 < r) (hr₁ : r < 1) :
    0 < -Real.log (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr₁' : (r : ℝ) < 1 := by exact_mod_cast hr₁
  exact neg_pos.mpr (Real.log_neg hr' hr₁')

private lemma buffer_geometric_exp_identity (r : ℚ) (hr : 0 < r) (b : ℕ) :
    Real.exp (-(-Real.log (r : ℝ)) * (b : ℝ)) = (r : ℝ)^b := by
  rw [neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hr)]

private lemma buffer_rational_stopping_iff_real
    (J g C τ ζ r : ℚ) (m s b : ℕ) :
    (4 * J / g) * (16 * ((m : ℚ) + C * ((s : ℚ) + b + 1)^3)^2 / τ) * r^b ≤ ζ^2 / 2 ↔
    (4 * (J : ℝ) / g) * (16 * ((m : ℝ) + C * ((s : ℝ) + b + 1)^3)^2 / τ) * (r : ℝ)^b ≤
      (ζ : ℝ)^2 / 2 := by
  exact_mod_cast Iff.rfl

/-- A rational comparison that can be evaluated using exact arithmetic. -/
def rationalTest (r J g C τ ζ : ℚ) (m s b : ℕ) : Prop :=
  (4 * J / g) * (16 * ((m : ℚ) + C * ((s : ℚ) + b + 1)^3)^2 / τ) * r^b ≤ ζ^2 / 2

instance (r J g C τ ζ : ℚ) (m s : ℕ) : DecidablePred (rationalTest r J g C τ ζ m s) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The real logarithmic witness proves termination of exact rational search. -/
theorem rationalTest_witness (r J g C τ ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    rationalTest r J g C τ ζ m s (choice (-Real.log r) J g C m s τ ζ) := by
  let μ := -Real.log (r : ℝ)
  let b := choice μ J g C m s τ ζ
  have hμ := buffer_geometric_decay_rate_pos r hr hr1
  have hJ' : (0 : ℝ) ≤ J := by exact_mod_cast hJ
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hC' : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hτ1' : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hζ' : (0 : ℝ) < ζ := by exact_mod_cast hζ
  have hζ1' : (ζ : ℝ) ≤ 1 := by exact_mod_cast hζ1
  have hh := feedback_volume_bound μ J g C hμ hJ' hg' hC' m s b
    ((C : ℝ) * ((s : ℝ) + b + 1)^3) (by positivity)
    (choice_one_le μ J g C m s τ ζ) τ ζ hτ' hζ' le_rfl
    (choice_exponential_bound μ J g C hμ hJ' hg' m s τ ζ hτ' hτ1' hζ' hζ1')
  rw [show Real.exp (-μ * (b : ℝ)) = (r : ℝ)^b from buffer_geometric_exp_identity r hr b] at hh
  exact (buffer_rational_stopping_iff_real J g C τ ζ r m s b).mpr hh

/-- Exact rational search; no transcendental evaluation is needed by this
implementation. Its termination proof uses the explicit logarithmic witness. -/
def rationalChoice (r J g C τ ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : ℕ :=
  Nat.find ⟨_, rationalTest_witness r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1⟩

theorem rationalChoice_spec (r J g C τ ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    rationalTest r J g C τ ζ m s
      (rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1) :=
  Nat.find_spec _

theorem rationalChoice_le_choice (r J g C τ ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1 ≤
      choice (-Real.log r) J g C m s τ ζ :=
  Nat.find_min' _ (rationalTest_witness r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1)

/-- The executable buffer obeys the same explicit logarithmic upper bound. -/
theorem rationalChoice_logarithmic_bound (r J g C τ ζ : ℚ) (m s : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1 : ℝ) ≤
      2 + (2 / (-Real.log (r : ℝ))) *
      (Real.log (fixedConstant (-Real.log r) J g C) + 2 * Real.log ((m : ℝ) + 1) +
       6 * Real.log ((s : ℝ) + 1) + Real.log (1 / (τ : ℝ)) + 2 * Real.log (1 / (ζ : ℝ))) := by
  have hh : (rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1 : ℝ) ≤
      choice (-Real.log r) J g C m s τ ζ := by
    exact_mod_cast rationalChoice_le_choice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1
  exact hh.trans (choice_logarithmic_bound (-Real.log r) J g C
    (buffer_geometric_decay_rate_pos r hr hr1) (by exact_mod_cast hJ) (by exact_mod_cast hg)
    m s τ ζ (by exact_mod_cast hτ) (by exact_mod_cast hτ1) (by exact_mod_cast hζ) (by exact_mod_cast hζ1))

/-- A successful rational test controls the physical exponential whenever
its rational geometric base bounds the one-layer physical decay. -/
theorem rationalTest_feedback_bound (r J g C τ ζ : ℚ) (m s b N : ℕ)
    (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C) (hτ : 0 < τ)
    (μ : ℝ) (htail : Real.exp (-μ) ≤ (r : ℝ))
    (hN : (N : ℝ) ≤ (C : ℝ) * ((s : ℝ) + b + 1)^3)
    (hstop : rationalTest r J g C τ ζ m s b) :
    (4 * (J : ℝ) / g) * (16 * ((m : ℝ) + N)^2 / τ) * Real.exp (-μ * b) ≤
      (ζ : ℝ)^2 / 2 := by
  have hJ' : (0 : ℝ) ≤ J := by exact_mod_cast hJ
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hC' : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hexp : Real.exp (-μ * b) ≤ (r : ℝ)^b := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le htail b
  calc
    _ ≤ (4 * (J : ℝ) / g) *
        (16 * ((m : ℝ) + (C : ℝ) * ((s : ℝ) + b + 1)^3)^2 / τ) * Real.exp (-μ * b) := by
      gcongr
    _ ≤ (4 * (J : ℝ) / g) *
        (16 * ((m : ℝ) + (C : ℝ) * ((s : ℝ) + b + 1)^3)^2 / τ) * (r : ℝ)^b :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ _ := (buffer_rational_stopping_iff_real J g C τ ζ r m s b).mp hstop

/-- Executable choice, actual dimension feedback, and physical decay in one
statement, with no remaining buffer-success premise. -/
theorem rationalChoice_feedback_bound (r J g C τ ζ : ℚ) (m s N : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hJ : 0 ≤ J) (hg : 0 < g) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (μ : ℝ) (htail : Real.exp (-μ) ≤ (r : ℝ))
    (hN : (N : ℝ) ≤ (C : ℝ) * ((s : ℝ) +
      rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1 + 1)^3) :
    (4 * (J : ℝ) / g) * (16 * ((m : ℝ) + N)^2 / τ) *
      Real.exp (-μ * rationalChoice r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1) ≤
      (ζ : ℝ)^2 / 2 :=
  rationalTest_feedback_bound r J g C τ ζ m s _ N hJ hg hC hτ μ htail hN
    (rationalChoice_spec r J g C τ ζ m s hr hr1 hJ hg hC hτ hτ1 hζ hζ1)

end
end Maxwell.Realization.Buffer
