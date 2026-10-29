import Maxwell.Defect.ModeSchedule

/-! Rational bounded-precision approximation of the selected simple mode.
The fixed startup data determine linear power, input, and normalization
precision schedules. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End

variable {n : ℕ}

def rationalModeApproximation
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C target M B p ρ : ℚ)
    (hB : 0 < B) (hp : 0 < p) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (v : Fin n → ℚ) (b : ℕ) : Fin n → ℚ :=
  let N := modeDegree B p ρ hB hp hρ hρ1 b
  let A := rationalModeFilter (T (filterInputPrecision C M N)) target ((M ^ 2)⁻¹)
  RationalNormalize.vector (rationalPowerAction A N v) (2 ^ N * B)
    (modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)

set_option maxHeartbeats 800000 in
theorem rationalModeApproximation_spec
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : S.toLinearMap.IsSymmetric)
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C target M B p ρ : ℚ)
    (hM : 0 < M) (hC : 0 ≤ C) (hB : 0 < B) (hp : 0 < p)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (μ β : ℝ)
    (hβ : 0 ≤ β)
    (hα : 1 / 2 ≤ scalarModeFilter target ((M : ℝ)^2)⁻¹ μ)
    (hβα : β ≤ (ρ : ℝ) * scalarModeFilter target ((M : ℝ)^2)⁻¹ μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target ((M : ℝ)^2)⁻¹ (hS.eigenvalues rfl i)| ≤ β)
    (hnorm : ‖S‖ + |(target : ℝ)| ≤ (M : ℝ))
    (herr : ∀ b, ‖S - rationalOperator (T b)‖ ≤ (C : ℝ) * (1 / 2 : ℝ)^b)
    (v : Fin n → ℚ) (hv : ‖rationalVector v‖ ≤ (B : ℝ))
    (hproj : (p : ℝ) ≤ ‖selectedProjection S μ (rationalVector v)‖) (b : ℕ) :
    ‖rationalVector (rationalModeApproximation T C target M B p ρ hB hp hρ hρ1 v b)‖ ≤ 1 ∧
    ‖rationalVector (rationalModeApproximation T C target M B p ρ hB hp hρ hρ1 v b) -
      NormedSpace.normalize (selectedProjection S μ (rationalVector v))‖ ≤ (1 / 2 : ℝ)^b := by
  let N := modeDegree B p ρ hB hp hρ hρ1 b
  let A := rationalModeFilter (T (filterInputPrecision C M N)) target ((M ^ 2)⁻¹)
  let F := modeFilter S target ((M : ℝ)^2)⁻¹
  let x := rationalVector v
  let P := selectedProjection S μ x
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hP : P ≠ 0 := norm_pos_iff.mp (hp'.trans_le hproj)
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := ⟨⟨P, 0, hP⟩⟩
  have hFnorm : ‖F‖ ≤ 1 := modeFilter_norm_of_bound S hS target M
    (by exact_mod_cast hM) hnorm
  have hA : ‖F - rationalOperator A‖ ≤ (1 / 16 : ℝ)^N :=
    rationalModeFilter_binary_error S T C target M hM hC hnorm herr N
  have hAnorm : ‖rationalOperator A‖ ≤ 2 := by
    have he : ‖F - rationalOperator A‖ ≤ 1 := hA.trans
      (pow_le_one₀ (by norm_num) (by norm_num))
    have ht := norm_le_norm_add_norm_sub F (rationalOperator A)
    linarith
  have hdegree : (2 * (B : ℝ) / (p : ℝ)) * ((1 / 2 : ℝ)^N + (ρ : ℝ)^N) ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ)^b := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (modeDegree_error B p ρ hB hp hρ hρ1 b)
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_one,
      Rat.cast_ofNat] using hh
  have hsmall : ((1 / 2 : ℝ)^N + (ρ : ℝ)^N) * ‖x‖ ≤ (p : ℝ) / 2 := by
    have hd := mul_le_mul_of_nonneg_right hdegree hp'.le
    have hbin : (1 / 2 : ℝ)^b ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hd' : 2 * (B : ℝ) * ((1 / 2 : ℝ)^N + (ρ : ℝ)^N) ≤ (p : ℝ) / 4 := by
      field_simp at hd
      nlinarith
    have hx := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ (1 / 2 : ℝ)^N + (ρ : ℝ)^N by positivity)
    nlinarith
  have hlower := filteredVector_norm_lower S hS target ((M : ℝ)^2)⁻¹ μ β ρ hβ hρ'
    hα hβα hfilter hFnorm (rationalOperator A) hAnorm N hA x p hp'.le hproj hsmall
  have hupper : ‖((rationalOperator A)^N) x‖ ≤ (2 : ℝ)^N * (B : ℝ) := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul _ hv (norm_nonneg _) (by positivity)
    exact (norm_pow_le _ N).trans (pow_le_pow_left₀ (norm_nonneg _) hAnorm N)
  have hpow : rationalVector (rationalPowerAction A N v) = ((rationalOperator A)^N) x :=
    rationalPowerAction_operator A N v
  have hlo : (((1 / 2 : ℚ)^N * p / 2 : ℚ) : ℝ) ≤
      ‖rationalVector (rationalPowerAction A N v)‖ := by
    rw [hpow]
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using hlower
  have hhi : ‖rationalVector (rationalPowerAction A N v)‖ ≤ ((2 ^ N * B : ℚ) : ℝ) := by
    rw [hpow]
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hupper
  obtain ⟨hnormout, hnormerr⟩ := RationalNormalize.vector_spec (rationalPowerAction A N v)
    (2 ^ N * B) ((1 / 2 : ℚ)^N * p / 2)
    (modeNormalizationPrecision B p ρ hB hp hρ hρ1 b) (by positivity) (by positivity) hlo hhi
  have hnormbudget :
      (((2 ^ N * B) / ((1 / 2 : ℚ)^N * p / 2) : ℚ) : ℝ) *
      ((2 : ℝ)^modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)⁻¹ ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ)^b := by
    have hh := (Rat.cast_le (K := ℝ)).mpr
      (modeNormalizationPrecision_error B p ρ hB hp hρ hρ1 b)
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_inv, Rat.cast_one,
      Rat.cast_ofNat] using hh
  have hfiltererr := normalized_modeFilter_binary_error S hS target ((M : ℝ)^2)⁻¹ μ β ρ
    hβ hρ' hα hβα hfilter hFnorm (rationalOperator A) hAnorm N hA x hP
  have hfilterbudget : ‖NormedSpace.normalize (((rationalOperator A)^N) x) -
      NormedSpace.normalize P‖ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ)^b := by
    apply hfiltererr.trans
    apply le_trans _ hdegree
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hv (by norm_num)) hp' hproj
  refine ⟨hnormout, ?_⟩
  change ‖rationalVector (RationalNormalize.vector (rationalPowerAction A N v) (2 ^ N * B)
      (modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)) - NormedSpace.normalize P‖ ≤ _
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (rationalVector (RationalNormalize.vector (rationalPowerAction A N v) (2 ^ N * B)
      (modeNormalizationPrecision B p ρ hB hp hρ hρ1 b)))
    (NormedSpace.normalize (rationalVector (rationalPowerAction A N v))) (NormedSpace.normalize P)
  rw [hpow] at ht hnormerr
  linarith [hnormerr.trans hnormbudget, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) b]

end Maxwell.Defect
