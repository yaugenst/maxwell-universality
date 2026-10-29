import Maxwell.Defect.RationalResidual
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic

/-! Rational square-root weights and certified weighted compressions. -/
namespace Maxwell.Defect

open Matrix Filter Topology

variable {n : ℕ}

/-- Nonnegative rational square bounds certify the actual square root. -/
theorem rational_sqrt_enclosure_sound (W a b : ℚ)
    (ha : 0 ≤ a) (hab : a ≤ b) (haW : a ^ 2 ≤ W) (hWb : W ≤ b ^ 2) :
    (a : ℝ) ≤ Real.sqrt (W : ℝ) ∧ Real.sqrt (W : ℝ) ≤ (b : ℝ) := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast ha.trans hab
  have hW0 : (0 : ℝ) ≤ W := by exact_mod_cast (sq_nonneg a).trans haW
  have hasq : (a : ℝ) ^ 2 ≤ W := by exact_mod_cast haW
  have hbsq : (W : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hWb
  have hs := Real.sq_sqrt hW0
  constructor <;> nlinarith [Real.sqrt_nonneg (W : ℝ)]

/-- The executable squared-error check avoids division by a small weight. -/
theorem sqrt_error_of_squared_error (W r δ : ℝ) (hW : 0 ≤ W) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hcheck : |r ^ 2 - W| ≤ δ ^ 2) :
    |r - Real.sqrt W| ≤ δ := by
  have hs := Real.sq_sqrt hW
  have hs0 := Real.sqrt_nonneg W
  obtain ⟨hl, hu⟩ := abs_le.mp hcheck
  apply abs_le.mpr
  constructor
  · by_contra h
    have hh : r + δ < Real.sqrt W := by linarith
    have hsq := sq_lt_sq₀ (by positivity : 0 ≤ r + δ) hs0 |>.mpr hh
    nlinarith [mul_nonneg hr hδ]
  · by_contra h
    have hh : Real.sqrt W + δ < r := by linarith
    have hsq := sq_lt_sq₀ (by positivity : 0 ≤ Real.sqrt W + δ) hr |>.mpr hh
    nlinarith [mul_nonneg hs0 hδ]

theorem rational_sqrt_error (W r δ : ℚ) (hW : 0 ≤ W) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (hcheck : |r ^ 2 - W| ≤ δ ^ 2) :
    |(r : ℝ) - Real.sqrt (W : ℝ)| ≤ (δ : ℝ) := by
  apply sqrt_error_of_squared_error
  · exact_mod_cast hW
  · exact_mod_cast hr
  · exact_mod_cast hδ
  · exact_mod_cast hcheck

/-- Rational endpoints with arbitrarily small separation enclose each
weight's square root, including the endpoint weights zero and one. -/
theorem exists_rational_sqrt_enclosure (W δ : ℚ) (hW : 0 ≤ W) (hW1 : W ≤ 1)
    (hδ : 0 < δ) :
    ∃ a b : ℚ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ a ^ 2 ≤ W ∧ W ≤ b ^ 2 ∧ b - a < δ := by
  by_cases hzero : W = 0
  · exact ⟨0, 0, by simp [hzero, hδ]⟩
  by_cases hone : W = 1
  · exact ⟨1, 1, by simp [hone, hδ]⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast lt_of_le_of_ne hW (Ne.symm hzero)
  have hW1r : (W : ℝ) < 1 := by exact_mod_cast lt_of_le_of_ne hW1 hone
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hs0 : 0 < Real.sqrt (W : ℝ) := Real.sqrt_pos.mpr hWr
  have hs1 : Real.sqrt (W : ℝ) < 1 := by
    have hs := Real.sq_sqrt hWr.le
    nlinarith [Real.sqrt_nonneg (W : ℝ)]
  obtain ⟨a, haL, haU⟩ := exists_rat_btwn (show
      max 0 (Real.sqrt (W : ℝ) - (δ : ℝ) / 2) < Real.sqrt (W : ℝ) by
    exact max_lt hs0 (by linarith))
  obtain ⟨b, hbL, hbU⟩ := exists_rat_btwn (show
      Real.sqrt (W : ℝ) < min 1 (Real.sqrt (W : ℝ) + (δ : ℝ) / 2) by
    exact lt_min hs1 (by linarith))
  have ha0 : (0 : ℝ) ≤ a := (le_max_left _ _).trans haL.le
  have hb1 : (b : ℝ) ≤ 1 := hbU.le.trans (min_le_left _ _)
  have hab : (a : ℝ) ≤ b := haU.le.trans hbL.le
  have hasq : (a : ℝ) ^ 2 ≤ W := by nlinarith [Real.sq_sqrt hWr.le]
  have hbsq : (W : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith [Real.sq_sqrt hWr.le]
  have hwidth : (b : ℝ) - a < δ := by
    have hal := (le_max_right _ _).trans_lt haL
    have hbu := hbU.trans_le (min_le_right _ _)
    linarith
  exact ⟨a, b, by exact_mod_cast ha0, by exact_mod_cast hab,
    by exact_mod_cast hb1, by exact_mod_cast hasq, by exact_mod_cast hbsq,
    by exact_mod_cast hwidth⟩

/-- Every positive rational precision admits a rational weight proposal
passing the finite squared-error check. -/
theorem exists_rational_sqrt_proposal (W δ : ℚ) (hW : 0 ≤ W) (hW1 : W ≤ 1)
    (hδ : 0 < δ) : ∃ r : ℚ, 0 ≤ r ∧ r ≤ 1 ∧ |r ^ 2 - W| ≤ δ ^ 2 := by
  obtain ⟨a, b, ha, hab, hb, haW, hWb, hwidth⟩ :=
    exists_rational_sqrt_enclosure W (δ ^ 2 / 2) hW hW1 (by positivity)
  refine ⟨a, ha, hab.trans hb, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr haW)]
  have hs := mul_le_mul_of_nonneg_right (show a + b ≤ 2 by linarith) (sub_nonneg.mpr hab)
  nlinarith

theorem exists_finite_rational_sqrt_proposal (W : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 < δ) :
    ∃ r : Fin n → ℚ, ∀ i, 0 ≤ r i ∧ r i ≤ 1 ∧ |r i ^ 2 - W i| ≤ δ ^ 2 := by
  choose r hr using fun i => exists_rational_sqrt_proposal (W i) δ (hW i) (hW1 i) hδ
  exact ⟨r, hr⟩

theorem exists_finite_rational_sqrt_enclosure (W : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 < δ) :
    ∃ a b : Fin n → ℚ, ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1 ∧
      a i ^ 2 ≤ W i ∧ W i ≤ b i ^ 2 ∧ b i - a i < δ := by
  choose a b hab using fun i => exists_rational_sqrt_enclosure (W i) δ (hW i) (hW1 i) hδ
  exact ⟨a, b, hab⟩

@[simp] theorem weight_diagonal_apply (d : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : euclideanOperator (Matrix.diagonal d) x i = d i * x i := by
  change (Matrix.diagonal d).toEuclideanLin x i = _
  simp [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

/-- A coordinatewise bound controls the genuine Euclidean operator norm. -/
theorem weight_diagonal_norm_le (d : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, |d i| ≤ B) : ‖euclideanOperator (Matrix.diagonal d)‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  have hs : ‖euclideanOperator (Matrix.diagonal d) x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, weight_diagonal_apply, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := pow_le_pow_left₀ (abs_nonneg (d i)) (hd i) 2
    rw [sq_abs] at hi
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hi (sq_nonneg (x i))
  nlinarith [norm_nonneg (euclideanOperator (Matrix.diagonal d) x),
    mul_nonneg hB (norm_nonneg x)]

noncomputable def sqrtWeightOperator (W : Fin n → ℚ) :=
  euclideanOperator (Matrix.diagonal (fun i => Real.sqrt (W i : ℝ)))

def rationalWeightedMatrix (T : Matrix (Fin n) (Fin n) ℚ) (r : Fin n → ℚ) :=
  Matrix.diagonal r * T * Matrix.diagonal r

theorem rationalOperator_diagonal (r : Fin n → ℚ) :
    rationalOperator (Matrix.diagonal r) = euclideanOperator (Matrix.diagonal (fun i => (r i : ℝ))) := by
  change euclideanOperator (rationalMatrixCast (Matrix.diagonal r)) = _
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h]

theorem rationalWeightedMatrix_isSymm (T : Matrix (Fin n) (Fin n) ℚ)
    (r : Fin n → ℚ) (hT : T.IsSymm) : (rationalWeightedMatrix T r).IsSymm := by
  change (rationalWeightedMatrix T r).transpose = rationalWeightedMatrix T r
  simp only [rationalWeightedMatrix, Matrix.transpose_mul, Matrix.diagonal_transpose,
    hT.eq, mul_assoc]

theorem rational_weight_operator_bounds (W r : Fin n → ℚ) (δ : ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 ≤ δ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1 ∧ |r i ^ 2 - W i| ≤ δ ^ 2) :
    ‖sqrtWeightOperator W‖ ≤ 1 ∧ ‖rationalOperator (Matrix.diagonal r)‖ ≤ 1 ∧
      ‖rationalOperator (Matrix.diagonal r) - sqrtWeightOperator W‖ ≤ (δ : ℝ) := by
  have hW0r : ∀ i, (0 : ℝ) ≤ W i := fun i => by exact_mod_cast hW i
  have hW1r : ∀ i, (W i : ℝ) ≤ 1 := fun i => by exact_mod_cast hW1 i
  refine ⟨?_, ?_, ?_⟩
  · apply weight_diagonal_norm_le _ 1 zero_le_one
    intro i
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sq_sqrt (hW0r i)
    nlinarith [Real.sqrt_nonneg (W i : ℝ), hW1r i]
  · rw [rationalOperator_diagonal]
    apply weight_diagonal_norm_le _ 1 zero_le_one
    intro i
    have hri : (0 : ℝ) ≤ r i := by exact_mod_cast (hr i).1
    rw [abs_of_nonneg hri]
    exact_mod_cast (hr i).2.1
  · rw [rationalOperator_diagonal, sqrtWeightOperator, ← map_sub, Matrix.diagonal_sub]
    apply weight_diagonal_norm_le _ (δ : ℝ) (by exact_mod_cast hδ)
    intro i
    exact rational_sqrt_error (W i) (r i) δ (hW i) (hr i).1 hδ (hr i).2.2

/-- Compression by two contractions preserves the unweighted matrix error;
the additional weight error costs at most twice the true matrix norm. -/
theorem weighted_compression_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R T D L : E →L[ℝ] E) (ε δ M : ℝ)
    (hD : ‖D‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hRT : ‖T - R‖ ≤ ε)
    (hLD : ‖L - D‖ ≤ δ) (hR : ‖R‖ ≤ M) :
    ‖L * T * L - D * R * D‖ ≤ ε + 2 * M * δ := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hRT
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hLD
  have hM : 0 ≤ M := (norm_nonneg _).trans hR
  have hfirst : ‖L * (T - R) * L‖ ≤ ε := by
    calc
      _ ≤ ‖L‖ * ‖T - R‖ * ‖L‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ε * 1 := by gcongr
      _ = ε := by ring
  have hsecond : ‖(L - D) * R * L‖ ≤ δ * M := by
    calc
      _ ≤ ‖L - D‖ * ‖R‖ * ‖L‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ δ * M * 1 := by gcongr
      _ = δ * M := by ring
  have hthird : ‖D * R * (L - D)‖ ≤ M * δ := by
    calc
      _ ≤ ‖D‖ * ‖R‖ * ‖L - D‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * M * δ := by gcongr
      _ = M * δ := by ring
  have hid : L * T * L - D * R * D =
      L * (T - R) * L + (L - D) * R * L + D * R * (L - D) := by noncomm_ring
  rw [hid]
  calc
    _ ≤ (‖L * (T - R) * L‖ + ‖(L - D) * R * L‖) + ‖D * R * (L - D)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (ε + δ * M) + M * δ := add_le_add (add_le_add hfirst hsecond) hthird
    _ = ε + 2 * M * δ := by ring

/-- Fully rational weight checks and an unweighted matrix enclosure give
the operator-norm enclosure needed by the executable spectral checker. -/
theorem rational_weighted_compression_error
    (W r : Fin n → ℚ) (δ : ℚ) (T : Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (ε M : ℝ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) (hδ : 0 ≤ δ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1 ∧ |r i ^ 2 - W i| ≤ δ ^ 2)
    (hRT : ‖rationalOperator T - R‖ ≤ ε) (hR : ‖R‖ ≤ M) :
    ‖rationalOperator (rationalWeightedMatrix T r) -
      sqrtWeightOperator W * R * sqrtWeightOperator W‖ ≤ ε + 2 * M * (δ : ℝ) := by
  obtain ⟨hD, hL, hLD⟩ := rational_weight_operator_bounds W r δ hW hW1 hδ hr
  simp only [rationalWeightedMatrix, map_mul]
  exact weighted_compression_error R (rationalOperator T) (sqrtWeightOperator W)
    (rationalOperator (Matrix.diagonal r)) ε δ M hD hL hRT hLD hR

/-- The finite rational squared-error checks can be met along a fixed
precision schedule tending to zero in the actual operator norm. -/
theorem exists_rational_weight_sequence (W : Fin n → ℚ)
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) :
    ∃ r : ℕ → Fin n → ℚ,
      (∀ k i, 0 ≤ r k i ∧ r k i ≤ 1 ∧
        |r k i ^ 2 - W i| ≤ (1 / ((k : ℚ) + 1)) ^ 2) ∧
      Tendsto (fun k => rationalOperator (Matrix.diagonal (r k))) atTop
        (𝓝 (sqrtWeightOperator W)) := by
  choose r hr using fun k : ℕ => exists_finite_rational_sqrt_proposal W
    (1 / ((k : ℚ) + 1)) hW hW1 (by positivity)
  refine ⟨r, hr, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun k : ℕ => ((1 / ((k : ℚ) + 1) : ℚ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro k
  exact (rational_weight_operator_bounds W (r k) (1 / ((k : ℚ) + 1)) hW hW1
    (by positivity) (hr k)).2.2

/-- Any convergent sequence of symmetric rational unweighted matrices
induces symmetric rational weighted approximations converging to the true
square-root compression. -/
theorem exists_rational_weighted_compression_sequence (W : Fin n → ℚ)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hW : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1)
    (hT : ∀ k, (T k).IsSymm)
    (hlim : Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 R)) :
    ∃ r : ℕ → Fin n → ℚ,
      (∀ k i, 0 ≤ r k i ∧ r k i ≤ 1 ∧
        |r k i ^ 2 - W i| ≤ (1 / ((k : ℚ) + 1)) ^ 2) ∧
      (∀ k, (rationalWeightedMatrix (T k) (r k)).IsSymm) ∧
      Tendsto (fun k => rationalOperator (rationalWeightedMatrix (T k) (r k))) atTop
        (𝓝 (sqrtWeightOperator W * R * sqrtWeightOperator W)) := by
  obtain ⟨r, hr, hrlim⟩ := exists_rational_weight_sequence W hW hW1
  refine ⟨r, hr, fun k => rationalWeightedMatrix_isSymm (T k) (r k) (hT k), ?_⟩
  simpa only [rationalWeightedMatrix, map_mul] using (hrlim.mul hlim).mul hrlim

end Maxwell.Defect
