import Maxwell.Continuum.RationalSquareRootEvaluation
import Maxwell.Continuum.CornerBridgeTop

/-! Executable rational coefficients of the normalized corner seed.
The common normalization is evaluated from its literal algebraic formula. -/

namespace Maxwell.Continuum.Calibration

set_option maxHeartbeats 800000
set_option maxRecDepth 2048

def seedRadical (N : ℕ) : ℚ := sqrtNaturalCenter 19 (N+7)
def seedRaw (N : ℕ) : Fin 3 → ℚ :=
  ![(8+seedRadical N)/15, (1-seedRadical N)/6, (seedRadical N-7)/10]
def seedDenominatorSq (N : ℕ) : ℚ := 8*(361-28*seedRadical N)/225
def seedDenominator (N : ℕ) : ℚ := sqrtRationalCenter (seedDenominatorSq N) (N+7)
def seedComponent (N : ℕ) (j : Fin 3) : ℚ := seedRaw N j/seedDenominator N

noncomputable def exactSeedDenominator : ℝ :=
  Real.sqrt (8*dotProduct Corner.topVector Corner.topVector)

theorem seedRadical_bounds (N : ℕ) : (0 : ℝ) ≤ seedRadical N ∧ (seedRadical N : ℝ) ≤ 5 := by
  constructor
  · unfold seedRadical sqrtNaturalCenter
    positivity
  · exact (sqrtNatural_bracket 19 (N+7)).1.trans Corner.sqrt_nineteen_bounds.2.le

theorem seedRadical_error (N : ℕ) :
    |(seedRadical N : ℝ)-Real.sqrt 19| ≤ (1/2 : ℝ)^(N+7) := by
  have h := sqrtNatural_bracket 19 (N+7)
  norm_num only [Nat.cast_ofNat] at h
  change |(sqrtNaturalCenter 19 (N+7) : ℝ)-Real.sqrt 19| ≤ _
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith only [h.2]

theorem seedRaw_error (N : ℕ) (j : Fin 3) :
    |(seedRaw N j : ℝ)-Corner.topVector j| ≤ (1/2 : ℝ)^(N+7) := by
  have h := abs_le.mp (seedRadical_error N)
  have hp : (0 : ℝ) ≤ (1/2 : ℝ)^(N+7) := by positivity
  fin_cases j <;> norm_num [seedRaw, Corner.topVector] <;>
    rw [abs_le] <;> constructor <;> linarith only [h.1, h.2, hp]

theorem topVector_abs_le_one (j : Fin 3) : |Corner.topVector j| ≤ 1 := by
  have hs := Corner.sqrt_nineteen_bounds
  fin_cases j <;> norm_num [Corner.topVector] <;> rw [abs_le] <;>
    constructor <;> linarith only [hs.1, hs.2]

theorem seedDenominatorSq_bounds (N : ℕ) :
    (4 : ℚ) ≤ seedDenominatorSq N ∧ seedDenominatorSq N ≤ 16 := by
  have h := seedRadical_bounds N
  have h0 : (0 : ℚ) ≤ seedRadical N := by exact_mod_cast h.1
  have h5 : seedRadical N ≤ 5 := by exact_mod_cast h.2
  unfold seedDenominatorSq
  constructor <;> linarith only [h0, h5]

theorem seedDenominatorSq_error (N : ℕ) :
    |(seedDenominatorSq N : ℝ)-8*dotProduct Corner.topVector Corner.topVector| ≤
      (1/2 : ℝ)^(N+7) := by
  have h := abs_le.mp (seedRadical_error N)
  have hp : (0 : ℝ) ≤ (1/2 : ℝ)^(N+7) := by positivity
  rw [Corner.topVector_normSq]
  simp only [seedDenominatorSq, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith only [h.1, h.2, hp]

theorem exactSeedDenominator_lower : (2 : ℝ) ≤ exactSeedDenominator := by
  have hs := Corner.sqrt_nineteen_bounds.2
  apply (Real.le_sqrt (by norm_num)
    (mul_nonneg (by norm_num) Corner.topVector_normSq_pos.le)).mpr
  rw [Corner.topVector_normSq]
  nlinarith only [hs]

theorem seedDenominator_lower (N : ℕ) : (1 : ℝ) ≤ seedDenominator N :=
  sqrtRational_lower (seedDenominatorSq_bounds N).1 (N+7)

private theorem sqrt_difference {a b e : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (he : 0 ≤ e) (hs : |a^2-b^2| ≤ e) : |a-b| ≤ e := by
  have h := abs_le.mp hs
  have hab : 1 ≤ a+b := by linarith only [ha, hb]
  rw [abs_le]
  constructor
  · by_cases hba : b ≤ a
    · linarith only [hba, he]
    · have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hba)) (sub_nonneg.mpr hab)
      nlinarith only [hm, h.1]
  · by_cases hab' : a ≤ b
    · linarith only [hab', he]
    · have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hab')) (sub_nonneg.mpr hab)
      nlinarith only [hm, h.2]

theorem seedDenominator_error (N : ℕ) :
    |(seedDenominator N : ℝ)-exactSeedDenominator| ≤ 2*(1/2 : ℝ)^(N+7) := by
  have hr0 : (0 : ℚ) ≤ seedDenominatorSq N := by linarith only [(seedDenominatorSq_bounds N).1]
  have hr4 : (4 : ℝ) ≤ seedDenominatorSq N := by exact_mod_cast (seedDenominatorSq_bounds N).1
  have hs : (1 : ℝ) ≤ Real.sqrt (seedDenominatorSq N : ℝ) :=
    (Real.le_sqrt (by norm_num) (Rat.cast_nonneg.mpr hr0)).mpr (by norm_num; linarith only [hr4])
  have hx : (0 : ℝ) ≤ 8*dotProduct Corner.topVector Corner.topVector :=
    mul_nonneg (by norm_num) Corner.topVector_normSq_pos.le
  have he : |Real.sqrt (seedDenominatorSq N : ℝ)-exactSeedDenominator| ≤
      (1/2 : ℝ)^(N+7) := by
    apply sqrt_difference hs (le_trans (by norm_num) exactSeedDenominator_lower) (by positivity)
    rw [Real.sq_sqrt (Rat.cast_nonneg.mpr hr0), exactSeedDenominator, Real.sq_sqrt hx]
    exact seedDenominatorSq_error N
  have hr := sqrtRational_error (seedDenominatorSq N) hr0 (N+7)
  have ht := abs_add_le ((seedDenominator N : ℝ)-Real.sqrt (seedDenominatorSq N : ℝ))
    (Real.sqrt (seedDenominatorSq N : ℝ)-exactSeedDenominator)
  rw [sub_add_sub_cancel] at ht
  change |(seedDenominator N : ℝ)-Real.sqrt (seedDenominatorSq N : ℝ)| ≤ _ at hr
  linarith only [ht, hr, he]

theorem seedComponent_error (N : ℕ) (j : Fin 3) :
    |(seedComponent N j : ℝ)-Corner.topVector j/exactSeedDenominator| ≤
      3*(1/2 : ℝ)^(N+7) := by
  have hd := seedDenominator_lower N
  have hc := exactSeedDenominator_lower
  have hd0 : (0 : ℝ) < seedDenominator N := by linarith only [hd]
  have hc0 : (0 : ℝ) < exactSeedDenominator := by linarith only [hc]
  have heq : (seedComponent N j : ℝ)-Corner.topVector j/exactSeedDenominator =
      ((seedRaw N j : ℝ)-Corner.topVector j)/(seedDenominator N : ℝ)+
        Corner.topVector j*(exactSeedDenominator-(seedDenominator N : ℝ))/
          ((seedDenominator N : ℝ)*exactSeedDenominator) := by
    simp only [seedComponent, Rat.cast_div]
    field_simp
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_div, abs_mul, abs_sub_comm exactSeedDenominator,
    abs_of_pos hd0, abs_of_pos (mul_pos hd0 hc0)]
  have hfirst := (div_le_div_of_nonneg_right (seedRaw_error N j) hd0.le).trans
    (div_le_self (by positivity) hd)
  have hprod : (1 : ℝ) ≤ (seedDenominator N : ℝ)*exactSeedDenominator := by
    nlinarith only [mul_le_mul hd hc (by norm_num : (0 : ℝ) ≤ 2) hd0.le]
  have hnum := mul_le_mul (topVector_abs_le_one j) (seedDenominator_error N)
    (abs_nonneg _) zero_le_one
  simp only [one_mul] at hnum
  have hsecond := (div_le_div_of_nonneg_right hnum (mul_pos hd0 hc0).le).trans
    (div_le_self (by positivity) hprod)
  linarith only [hfirst, hsecond]

#print axioms seedComponent_error

end Maxwell.Continuum.Calibration
