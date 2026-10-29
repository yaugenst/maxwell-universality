import Maxwell.Realization.Precision
import Maxwell.Logical.SourceInverse

/-! Constructed source precision and inverse bounds from the input promise.
No selected precision, rounding-smallness, or source inverse bound is assumed. -/
namespace Maxwell.Realization

/-- Polynomial logical inverse scale, encoded by exact rational arithmetic. -/
def logicalScale (m k : ℕ) : ℚ := (m : ℚ)^(k+1)

/-- The fixed integer accuracy exponent makes the grid independent of the
arbitrary requested accuracy presented to the theorem. -/
def logicalAccuracy (m c : ℕ) : ℚ := 1/(m:ℚ)^c

def coefficientBudget (m k c : ℕ) : ℚ :=
  logicalAccuracy m c / (64*(m:ℚ)*logicalScale m k)

theorem logicalScale_pos (m k : ℕ) (hm : 0 < m) : 0 < logicalScale m k := by
  unfold logicalScale
  positivity

theorem logicalAccuracy_pos (m c : ℕ) (hm : 0 < m) : 0 < logicalAccuracy m c := by
  unfold logicalAccuracy
  positivity

theorem coefficientBudget_pos (m k c : ℕ) (hm : 0 < m) : 0 < coefficientBudget m k c := by
  have hL := logicalScale_pos m k hm
  have he := logicalAccuracy_pos m c hm
  unfold coefficientBudget
  positivity

def coefficientPrecision (m k c : ℕ) (hm : 0 < m) : ℕ :=
  precisionBits (coefficientBudget m k c) (coefficientBudget_pos m k c hm)

theorem logicalScale_ge_one (m k : ℕ) (hm : 1 ≤ m) : 1 ≤ logicalScale m k :=
  one_le_pow₀ (by exact_mod_cast hm)

theorem logicalAccuracy_le_one (m c : ℕ) (hm : 1 ≤ m) : logicalAccuracy m c ≤ 1 := by
  have h := logicalScale_ge_one m c hm
  unfold logicalAccuracy
  exact (div_le_one (pow_pos (by exact_mod_cast (show 0<m by omega)) _)).mpr
    (one_le_pow₀ (by exact_mod_cast hm))

theorem coefficientPrecision_pos (m k c : ℕ) (hm : 2 ≤ m) :
    1 ≤ coefficientPrecision m k c (by omega) := by
  have hu := precisionUnit_le (coefficientBudget m k c) (coefficientBudget_pos m k c (by omega))
  have he := logicalAccuracy_le_one m c (by omega)
  have hL := logicalScale_ge_one m k (by omega)
  have hmQ : (2:ℚ)≤m := by exact_mod_cast hm
  have hbudget : coefficientBudget m k c < 1 := by
    unfold coefficientBudget
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  by_contra hnot
  have hz : coefficientPrecision m k c (by omega) = 0 := by omega
  change precisionBits (coefficientBudget m k c) (coefficientBudget_pos m k c (by omega)) = 0 at hz
  rw [precisionUnit, hz] at hu
  norm_num at hu
  exact (not_le_of_gt hbudget) hu

/-- The actual dyadic source precision achieves the literal unit budget. -/
theorem coefficientPrecision_unit (m k c : ℕ) (hm : 0 < m) :
    (1:ℝ)/2^(coefficientPrecision m k c hm) ≤
      (logicalAccuracy m c:ℝ)/(64*(m:ℝ)*(logicalScale m k:ℝ)) := by
  have h := precisionUnit_le (coefficientBudget m k c) (coefficientBudget_pos m k c hm)
  change (1:ℚ)/2^(coefficientPrecision m k c hm) ≤ coefficientBudget m k c at h
  have hc := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [coefficientBudget, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hc

/-- Matrix-rounding error is smaller than the required inverse-scale budget. -/
theorem coefficientPrecision_matrix_error (m k c : ℕ) (hm : 0 < m) :
    (m:ℝ)/(2*2^(coefficientPrecision m k c hm)) ≤
      (logicalAccuracy m c:ℝ)/(128*(logicalScale m k:ℝ)) := by
  have h := mul_le_mul_of_nonneg_left (coefficientPrecision_unit m k c hm)
    (show (0:ℝ)≤m/2 by positivity)
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  convert h using 1 <;> field_simp
  ring

/-- The normalized-system Neumann hypothesis follows from the promise and
selected precision, with no separate smallness input. -/
theorem coefficientPrecision_small (m k c : ℕ) (hm : 2 ≤ m) (κ : ℝ)
    (hcondition : (m:ℝ)*κ ≤ (logicalScale m k:ℝ)) :
    ((m:ℝ)*κ)*((m:ℝ)/(2*2^(coefficientPrecision m k c (by omega)))) ≤ 1/2 := by
  have hm0 : 0<m := by omega
  have hL : (0:ℝ)<logicalScale m k := by exact_mod_cast logicalScale_pos m k hm0
  have he : (logicalAccuracy m c:ℝ)≤1 := by exact_mod_cast logicalAccuracy_le_one m c (by omega)
  have he0 : (0:ℝ)≤logicalAccuracy m c := by exact_mod_cast (logicalAccuracy_pos m c hm0).le
  have h := mul_le_mul hcondition (coefficientPrecision_matrix_error m k c hm0)
    (by positivity : (0:ℝ)≤(m:ℝ)/(2*2^(coefficientPrecision m k c hm0))) hL.le
  have hx : (logicalScale m k:ℝ)*((logicalAccuracy m c:ℝ)/(128*(logicalScale m k:ℝ))) =
      (logicalAccuracy m c:ℝ)/128 := by field_simp
  rw [hx] at h
  linarith

/-- Rounding the promise exponent upward gives the actual logical inverse
scale, for every source in the non-base range. -/
theorem promise_logicalScale (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 2 ≤ S.nnz) (hpromise : Source.Promises p S) :
    (S.nnz:ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤
      (logicalScale S.nnz ⌈p.conditionExponent⌉₊ : ℝ) := by
  have hm1 : (1:ℝ)≤S.nnz := by exact_mod_cast (show 1≤S.nnz by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hm1 (Nat.le_ceil p.conditionExponent)
  have h := mul_le_mul_of_nonneg_left (hpromise.2.1.trans hpow)
    (show (0:ℝ)≤S.nnz by positivity)
  simpa only [Real.rpow_natCast, logicalScale, Rat.cast_pow, Rat.cast_natCast, Rat.cast_mul,
    pow_succ, mul_comm] using h

/-- The actual source circuit is invertible with the paper's16 L d⁴ bound
at the precision chosen from the original input promise. -/
theorem promised_source_inverse (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 2 ≤ S.nnz) (hpromise : Source.Promises p S) :
    let bits := coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega)
    let L := (logicalScale S.nnz ⌈p.conditionExponent⌉₊ : ℝ)
    ∃ e : EuclideanSpace ℝ (Fin (Logical.sourceCircuit S bits).size) ≃L[ℝ]
          EuclideanSpace ℝ (Fin (Logical.sourceCircuit S bits).size),
      (∀ x, e x = Logical.sourceSquareOperator S bits x) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ 16*L*((Logical.sourceCircuit S bits).size:ℝ)^4 := by
  dsimp only
  let bits := coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega)
  have hs : 1≤bits := coefficientPrecision_pos _ _ _ hm
  have hcond := promise_logicalScale p S hm hpromise
  have hsmall := coefficientPrecision_small S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ hm
    (Maxwell.condition₂ (Source.realMatrix S)) hcond
  refine ⟨Logical.sourceSquareEuclideanEquiv S hpromise.1 hm bits hs hsmall,
    (fun _ => rfl), ?_⟩
  apply Logical.sourceSquare_inverse_norm_le S hpromise.1 hm bits hs hsmall _ _ hcond
  exact_mod_cast logicalScale_ge_one S.nnz ⌈p.conditionExponent⌉₊ (by omega)

/-- The source coefficient budget is an exact inverse polynomial. -/
theorem coefficientBudget_inverse (m k c : ℕ) (hm : 0 < m) :
    (coefficientBudget m k c)⁻¹ = 64*(m:ℚ)^(k+c+2) := by
  have hm0 : (m:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold coefficientBudget logicalAccuracy logicalScale
  simp only [inv_div, div_div, div_one]
  have he : k+c+2 = c+(k+1)+1 := by omega
  rw [he, pow_add, pow_add, pow_one]
  ring

/-- Source arithmetic precision is logarithmic with a literal fixed
coefficient depending only on the promise exponents. -/
theorem coefficientPrecision_le_log (m k c : ℕ) (hm : 2 ≤ m) :
    (coefficientPrecision m k c (by omega):ℝ) ≤
      7 + ((k+c+2:ℕ):ℝ)*Real.log m/Real.log 2 := by
  have hm0 : 0<m := by omega
  have hinv : (coefficientBudget m k c:ℝ)⁻¹ = 64*(m:ℝ)^(k+c+2) := by
    exact_mod_cast coefficientBudget_inverse m k c hm0
  have h := precisionBits_le_polynomial (coefficientBudget m k c) (coefficientBudget_pos m k c hm0)
    64 ((k+c+2:ℕ):ℝ) m (by norm_num) (by positivity) (by exact_mod_cast (show 1≤m by omega))
    (by rw [Real.rpow_natCast, hinv])
  have hlog : Real.log (64:ℝ) = 6*Real.log 2 := by
    have ht := Real.log_pow (2:ℝ) 6
    norm_num at ht
    exact ht
  rw [hlog] at h
  change (coefficientPrecision m k c hm0:ℝ)≤_ at h
  have hl : Real.log (2:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  convert h using 1
  field_simp
  ring

/-- The actual allocated source circuit has the proved O(m log m) count
at its selected precision. -/
theorem promised_source_size (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 2 ≤ S.nnz) (hpromise : Source.Promises p S) :
    let bits := coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega)
    ((Logical.sourceCircuit S bits).size:ℝ) ≤
      6*(S.nnz:ℝ)*(8 + ((⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ):ℝ)*
        Real.log S.nnz/Real.log 2) := by
  dsimp only
  have hd := Logical.sourceCircuit_size S
    (coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega))
    (Source.dimension_le_nnz S hpromise.1)
  have hdr : ((Logical.sourceCircuit S
      (coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega))).size:ℝ) ≤
      6*(S.nnz:ℝ)*((coefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ (by omega):ℝ)+1) := by
    exact_mod_cast hd
  have hp := coefficientPrecision_le_log S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ hm
  exact hdr.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Maxwell.Realization
