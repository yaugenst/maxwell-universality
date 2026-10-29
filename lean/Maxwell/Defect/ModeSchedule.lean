import Maxwell.Defect.ModePrecision

/-! Fixed rational startup searches produce linear schedules for mode
filtering and normalization to any requested binary precision. -/
namespace Maxwell.Defect

theorem exists_modePrecisionBlock (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ k : ℕ, 0 < k ∧ ρ ^ k ≤ 1 / 2 ∧ (1 / 2 : ℚ) ^ k ≤ 1 / 2 ∧
      (2 * B / p) * ((1 / 2 : ℚ) ^ k + ρ ^ k) ≤ 1 / 4 := by
  let r : ℚ := max ρ (1 / 2)
  have hr1 : r < 1 := max_lt hρ1 (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (lt_min (by norm_num : (0 : ℚ) < 1 / 2) (div_pos hp (by positivity : 0 < 16 * B))) hr1
  have hkhalf : r ^ k < 1 / 2 := hk.trans_le (min_le_left _ _)
  have hkbudget : r ^ k ≤ p / (16 * B) := (hk.trans_le (min_le_right _ _)).le
  have hleft : ρ ^ k ≤ r ^ k := pow_le_pow_left₀ hρ (le_max_left _ _) k
  have hright : (1 / 2 : ℚ) ^ k ≤ r ^ k := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) k
  have hk0 : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    rw [he, pow_zero] at hkhalf
    norm_num at hkhalf
  refine ⟨k, hk0, hleft.trans hkhalf.le, hright.trans hkhalf.le, ?_⟩
  have hb : (16 * B) * r ^ k ≤ p := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 16 * B)).mp hkbudget
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_le_mul_of_nonneg_left hleft hB.le, mul_le_mul_of_nonneg_left hright hB.le]

def modePrecisionBlock (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) : ℕ :=
  Nat.find (exists_modePrecisionBlock B p ρ hB hp hρ hρ1)

def modeDegree (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) : ℕ :=
  modePrecisionBlock B p ρ hB hp hρ hρ1 * (b + 1)

def modeNormalizationPrecision (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) : ℕ :=
  2 * modeDegree B p ρ hB hp hρ hρ1 b + b + modePrecisionBlock B p ρ hB hp hρ hρ1

theorem modePrecisionBlock_spec (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    let k := modePrecisionBlock B p ρ hB hp hρ hρ1
    0 < k ∧ ρ ^ k ≤ 1 / 2 ∧ (1 / 2 : ℚ) ^ k ≤ 1 / 2 ∧
      (2 * B / p) * ((1 / 2 : ℚ) ^ k + ρ ^ k) ≤ 1 / 4 :=
  Nat.find_spec (exists_modePrecisionBlock B p ρ hB hp hρ hρ1)

theorem modeDegree_error (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) :
    let N := modeDegree B p ρ hB hp hρ hρ1 b
    (2 * B / p) * ((1 / 2 : ℚ) ^ N + ρ ^ N) ≤ (1 / 4 : ℚ) * (1 / 2 : ℚ) ^ b := by
  let k := modePrecisionBlock B p ρ hB hp hρ hρ1
  have hk := modePrecisionBlock_spec B p ρ hB hp hρ hρ1
  have hpw (r : ℚ) (hr : 0 ≤ r) (hrk : r ^ k ≤ 1 / 2) :
      r ^ modeDegree B p ρ hB hp hρ hρ1 b ≤ r ^ k * (1 / 2 : ℚ) ^ b := by
    change r ^ (k * (b + 1)) ≤ _
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hr k) hrk b) (pow_nonneg hr k)
  have hsum := add_le_add (hpw (1 / 2) (by norm_num) hk.2.2.1) (hpw ρ hρ hk.2.1)
  calc
    _ ≤ (2 * B / p) * (((1 / 2 : ℚ) ^ k + ρ ^ k) * (1 / 2 : ℚ) ^ b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [add_mul] using hsum
    _ = ((2 * B / p) * ((1 / 2 : ℚ) ^ k + ρ ^ k)) * (1 / 2 : ℚ) ^ b := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hk.2.2.2 (by positivity)

theorem modeNormalizationPrecision_error (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) :
    let N := modeDegree B p ρ hB hp hρ hρ1 b
    (2 ^ N * B / ((1 / 2 : ℚ) ^ N * p / 2)) *
      (2 ^ modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)⁻¹ ≤
        (1 / 4 : ℚ) * (1 / 2 : ℚ) ^ b := by
  let k := modePrecisionBlock B p ρ hB hp hρ hρ1
  let N := modeDegree B p ρ hB hp hρ hρ1 b
  have hk := modePrecisionBlock_spec B p ρ hB hp hρ hρ1
  have hb : (2 * B / p) * (1 / 2 : ℚ) ^ k ≤ 1 / 4 := by
    apply le_trans _ hk.2.2.2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_add_of_nonneg_right (pow_nonneg hρ _)
  have he : (2 ^ N * B / ((1 / 2 : ℚ) ^ N * p / 2)) *
      (2 ^ modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)⁻¹ =
      ((2 * B / p) * (1 / 2 : ℚ) ^ k) * (1 / 2 : ℚ) ^ b := by
    simp only [modeNormalizationPrecision, N, k, pow_add, pow_mul, one_div, inv_pow]
    field_simp
    ring_nf
    rw [Nat.mul_comm, pow_mul]
    norm_num
  exact he.le.trans (mul_le_mul_of_nonneg_right hb (by positivity))

theorem modeDegree_linear (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) :
    let k := modePrecisionBlock B p ρ hB hp hρ hρ1
    modeDegree B p ρ hB hp hρ hρ1 b = k * b + k := by
  simp only [modeDegree, Nat.mul_add, Nat.mul_one]

theorem modeInputPrecision_linear (C M B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) :
    let k := modePrecisionBlock B p ρ hB hp hρ hρ1
    filterInputPrecision C M (modeDegree B p ρ hB hp hρ hρ1 b) =
      (4 * k) * b + (4 * k + filterInputOffset C M) := by
  simp only [filterInputPrecision, modeDegree]
  ring

theorem modeNormalizationPrecision_linear (B p ρ : ℚ) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (b : ℕ) :
    let k := modePrecisionBlock B p ρ hB hp hρ hρ1
    modeNormalizationPrecision B p ρ hB hp hρ hρ1 b = (2 * k + 1) * b + 3 * k := by
  simp only [modeNormalizationPrecision, modeDegree]
  ring

end Maxwell.Defect
