import Maxwell.Defect.WeightEnclosure

/-! Bounded rational square-root computation by bisection. Each step uses
one midpoint, one square, and one exact comparison; no rational enumeration
or square-root oracle occurs in the algorithm. -/

namespace Maxwell.Defect.DyadicSqrt

/-- The rational interval update used by the finite algorithm. -/
def step (x : ℚ) (bounds : ℚ × ℚ) : ℚ × ℚ :=
  let middle := (bounds.1 + bounds.2) / 2
  if middle ^ 2 ≤ x then (middle, bounds.2) else (bounds.1, middle)

def interval (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | n + 1 => step x (interval x n)

def lower (x : ℚ) (n : ℕ) : ℚ := (interval x n).1

def upper (x : ℚ) (n : ℕ) : ℚ := (interval x n).2

theorem step_enclosure (x a b : ℚ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (ha2 : a ^ 2 ≤ x) (hb2 : x ≤ b ^ 2) :
    let next := step x (a, b)
    0 ≤ next.1 ∧ next.1 ≤ next.2 ∧ next.2 ≤ 1 ∧
      next.1 ^ 2 ≤ x ∧ x ≤ next.2 ^ 2 := by
  dsimp only [step]
  split_ifs with h
  · exact ⟨by linarith, by linarith, hb, h, hb2⟩
  · exact ⟨ha, by linarith, by linarith, ha2, (lt_of_not_ge h).le⟩

theorem step_width (x : ℚ) (bounds : ℚ × ℚ) :
    (step x bounds).2 - (step x bounds).1 = (bounds.2 - bounds.1) / 2 := by
  dsimp only [step]
  split_ifs <;> simp only <;> ring

/-- Every computed interval encloses the nonnegative square root and has
exact dyadic width. -/
theorem interval_spec (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ (interval x n).1 ∧ (interval x n).1 ≤ (interval x n).2 ∧
      (interval x n).2 ≤ 1 ∧ (interval x n).1 ^ 2 ≤ x ∧ x ≤ (interval x n).2 ^ 2 ∧
      (interval x n).2 - (interval x n).1 = ((2 : ℚ) ^ n)⁻¹ := by
  induction n with
  | zero => simp [interval, hx, hx1]
  | succ n ih =>
    obtain ⟨ha, hab, hb, ha2, hb2, hw⟩ := ih
    have hs := step_enclosure x (interval x n).1 (interval x n).2 ha hab hb ha2 hb2
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
    rw [interval, step_width, hw, pow_succ]
    ring

theorem lower_bounds (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ lower x n ∧ lower x n ≤ 1 := by
  have hs := interval_spec x hx hx1 n
  exact ⟨hs.1, hs.2.1.trans hs.2.2.1⟩

/-- After n bisections, the actual square-root error is at most 2^-n. -/
theorem sqrt_error (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |(lower x n : ℝ) - Real.sqrt (x : ℝ)| ≤ ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨ha, hab, _, ha2, hb2, hw⟩ := interval_spec x hx hx1 n
  have hroot := rational_sqrt_enclosure_sound x (interval x n).1 (interval x n).2 ha hab ha2 hb2
  unfold lower
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hroot.1)]
  calc
    _ ≤ ((interval x n).2 : ℝ) - (interval x n).1 := sub_le_sub_right hroot.2 _
    _ = _ := by
      have hcast := congrArg (fun q : ℚ => (q : ℝ)) hw
      simpa only [Rat.cast_sub, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hcast

/-- The upper endpoint encloses the actual root and has the same dyadic
error, allowing divisions that stay nonzero for every positive input. -/
theorem upper_sqrt_spec (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    Real.sqrt (x : ℝ) ≤ (upper x n : ℝ) ∧
      (upper x n : ℝ) - Real.sqrt (x : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ ∧ upper x n ≤ 1 := by
  obtain ⟨ha, hab, hb, ha2, hb2, hw⟩ := interval_spec x hx hx1 n
  have hroot := rational_sqrt_enclosure_sound x (interval x n).1 (interval x n).2 ha hab ha2 hb2
  refine ⟨hroot.2, ?_, hb⟩
  calc
    _ ≤ ((interval x n).2 : ℝ) - (interval x n).1 := sub_le_sub_left hroot.1 _
    _ = _ := by
      have hcast := congrArg (fun q : ℚ => (q : ℝ)) hw
      simpa only [Rat.cast_sub, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hcast

/-- The exact rational squared-error check also has a dyadic bound. -/
theorem squared_error (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |lower x n ^ 2 - x| ≤ 2 * ((2 : ℚ) ^ n)⁻¹ := by
  obtain ⟨ha, hab, hb, ha2, hb2, hw⟩ := interval_spec x hx hx1 n
  unfold lower
  rw [abs_of_nonpos (sub_nonpos.mpr ha2), ← hw]
  have hh := mul_le_mul_of_nonneg_right
    (show (interval x n).1 + (interval x n).2 ≤ 2 by linarith) (sub_nonneg.mpr hab)
  nlinarith

/-- Two p bits plus one bisection give the squared tolerance required by
the finite weight-enclosure checker. -/
def weight (x : ℚ) (p : ℕ) : ℚ := lower x (2 * p + 1)

theorem weight_spec (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (p : ℕ) :
    0 ≤ weight x p ∧ weight x p ≤ 1 ∧
      |weight x p ^ 2 - x| ≤ (((2 : ℚ) ^ p)⁻¹) ^ 2 := by
  obtain ⟨ha, hb⟩ := lower_bounds x hx hx1 (2 * p + 1)
  refine ⟨ha, hb, ?_⟩
  have hbound := squared_error x hx hx1 (2 * p + 1)
  have heq : 2 * ((2 : ℚ) ^ (2 * p + 1))⁻¹ = (((2 : ℚ) ^ p)⁻¹) ^ 2 := by
    rw [pow_add, pow_one, Nat.mul_comm 2 p, pow_mul]
    ring
  exact hbound.trans_eq heq

/-- The same bounded computation also satisfies the existing reciprocal
stage tolerance, so replacing the enumeration requires no error-bar change. -/
theorem weight_stage_spec (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    0 ≤ weight x k ∧ weight x k ≤ 1 ∧
      |weight x k ^ 2 - x| ≤ (1 / ((k : ℚ) + 1)) ^ 2 := by
  obtain ⟨ha, hb, he⟩ := weight_spec x hx hx1 k
  have hk : (k : ℚ) + 1 ≤ 2 ^ k := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := k)))
  have hδ : ((2 : ℚ) ^ k)⁻¹ ≤ 1 / ((k : ℚ) + 1) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℚ) < k + 1) hk
  exact ⟨ha, hb, he.trans (pow_le_pow_left₀ (by positivity) hδ 2)⟩

end Maxwell.Defect.DyadicSqrt
