import Maxwell.Realization.LogicalParameters
import Maxwell.Codec.Bounds

/-! An explicit source precision obtained from the length of the binary input
size. Unlike a search for a sufficient precision, this uses one word-length
scan and fixed-integer arithmetic, and has the same logarithmic bound. -/
namespace Maxwell.Realization

/-- The constants depend only on the fixed source promise. -/
def binaryCoefficientPrecision (m k c : ℕ) : ℕ :=
  7 + (k+c+2)*m.size

theorem binaryCoefficientPrecision_pos (m k c : ℕ) :
    1 ≤ binaryCoefficientPrecision m k c := by
  unfold binaryCoefficientPrecision
  omega

theorem binaryCoefficientPrecision_power (m k c : ℕ) :
    64*m^(k+c+2) ≤ 2^(binaryCoefficientPrecision m k c) := by
  have h := Nat.pow_le_pow_left (Nat.lt_size_self m).le (k+c+2)
  have hh : 64*m^(k+c+2) ≤ 128*(2^m.size)^(k+c+2) := by
    exact Nat.mul_le_mul (by norm_num) h
  have he : 2^(binaryCoefficientPrecision m k c) = 128*(2^m.size)^(k+c+2) := by
    rw [binaryCoefficientPrecision, pow_add, Nat.mul_comm (k+c+2) m.size, pow_mul]
    norm_num
  rw [he]
  exact hh

/-- Exact rational rounding budget, with no logarithm evaluation or search. -/
theorem binaryCoefficientPrecision_unit_rat (m k c : ℕ) (hm : 0 < m) :
    (1:ℚ)/2^(binaryCoefficientPrecision m k c) ≤ coefficientBudget m k c := by
  have hbudget := coefficientBudget_pos m k c hm
  have hp : (64:ℚ)*(m:ℚ)^(k+c+2) ≤ 2^(binaryCoefficientPrecision m k c) := by
    exact_mod_cast binaryCoefficientPrecision_power m k c
  rw [← coefficientBudget_inverse m k c hm] at hp
  have h := inv_le_inv₀ (by positivity :
    (0:ℚ)<2^(binaryCoefficientPrecision m k c)) (inv_pos.mpr hbudget)
  have hh := h.mpr hp
  simpa only [inv_inv, one_div] using hh

theorem binaryCoefficientPrecision_unit (m k c : ℕ) (hm : 0 < m) :
    (1:ℝ)/2^(binaryCoefficientPrecision m k c) ≤
      (logicalAccuracy m c:ℝ)/(64*(m:ℝ)*(logicalScale m k:ℝ)) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (binaryCoefficientPrecision_unit_rat m k c hm)
  simpa only [coefficientBudget, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using h

theorem binaryCoefficientPrecision_matrix_error (m k c : ℕ) (hm : 0 < m) :
    (m:ℝ)/(2*2^(binaryCoefficientPrecision m k c)) ≤
      (logicalAccuracy m c:ℝ)/(128*(logicalScale m k:ℝ)) := by
  have h := mul_le_mul_of_nonneg_left (binaryCoefficientPrecision_unit m k c hm)
    (show (0:ℝ)≤m/2 by positivity)
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  convert h using 1 <;> field_simp
  ring

theorem binaryCoefficientPrecision_small (m k c : ℕ) (hm : 2 ≤ m) (κ : ℝ)
    (hcondition : (m:ℝ)*κ ≤ (logicalScale m k:ℝ)) :
    ((m:ℝ)*κ)*((m:ℝ)/(2*2^(binaryCoefficientPrecision m k c))) ≤ 1/2 := by
  have hm0 : 0<m := by omega
  have hL : (0:ℝ)<logicalScale m k := by exact_mod_cast logicalScale_pos m k hm0
  have he : (logicalAccuracy m c:ℝ)≤1 := by
    exact_mod_cast logicalAccuracy_le_one m c (by omega)
  have h := mul_le_mul hcondition (binaryCoefficientPrecision_matrix_error m k c hm0)
    (by positivity : (0:ℝ)≤(m:ℝ)/(2*2^(binaryCoefficientPrecision m k c))) hL.le
  have hx : (logicalScale m k:ℝ)*((logicalAccuracy m c:ℝ)/(128*(logicalScale m k:ℝ))) =
      (logicalAccuracy m c:ℝ)/128 := by field_simp
  rw [hx] at h
  linarith

/-- Binary length is logarithmic, derived from its defining power inequality. -/
theorem nat_size_le_real_log (m : ℕ) (hm : 0 < m) :
    (m.size:ℝ) ≤ 1 + Real.log m / Real.log 2 := by
  have hs : 0 < m.size := Nat.size_pos.mpr hm
  have hpow : 2^(m.size-1) ≤ m := Nat.lt_size.mp (by omega)
  have hpowR : (2:ℝ)^(m.size-1) ≤ m := by exact_mod_cast hpow
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(m.size-1)) hpowR
  rw [Real.log_pow] at hl
  have hsub : ((m.size-1:ℕ):ℝ)+1 = (m.size:ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1≤m.size by omega)
  have hd := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl
  linarith

theorem binaryCoefficientPrecision_le_log (m k c : ℕ) (hm : 0 < m) :
    (binaryCoefficientPrecision m k c:ℝ) ≤
      7 + ((k+c+2:ℕ):ℝ)*(1 + Real.log m/Real.log 2) := by
  have h := mul_le_mul_of_nonneg_left (nat_size_le_real_log m hm)
    (show (0:ℝ) ≤ ((k+c+2:ℕ):ℝ) by positivity)
  simpa only [binaryCoefficientPrecision, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_comm]
    using add_le_add_left h 7

/-- Actual source-circuit invertibility at the explicitly generated precision. -/
theorem promised_binary_source_inverse (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 2 ≤ S.nnz) (hpromise : Source.Promises p S) :
    let bits := binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
    let L := (logicalScale S.nnz ⌈p.conditionExponent⌉₊ : ℝ)
    ∃ e : EuclideanSpace ℝ (Fin (Logical.sourceCircuit S bits).size) ≃L[ℝ]
          EuclideanSpace ℝ (Fin (Logical.sourceCircuit S bits).size),
      (∀ x, e x = Logical.sourceSquareOperator S bits x) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ 16*L*((Logical.sourceCircuit S bits).size:ℝ)^4 := by
  dsimp only
  let bits := binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
  have hs : 1≤bits := binaryCoefficientPrecision_pos _ _ _
  have hcond := promise_logicalScale p S hm hpromise
  have hsmall := binaryCoefficientPrecision_small S.nnz ⌈p.conditionExponent⌉₊
    ⌈p.accuracyExponent⌉₊ hm (Maxwell.condition₂ (Source.realMatrix S)) hcond
  refine ⟨Logical.sourceSquareEuclideanEquiv S hpromise.1 hm bits hs hsmall,
    (fun _ => rfl), ?_⟩
  apply Logical.sourceSquare_inverse_norm_le S hpromise.1 hm bits hs hsmall _ _ hcond
  exact_mod_cast logicalScale_ge_one S.nnz ⌈p.conditionExponent⌉₊ (by omega)

theorem promised_binary_source_size (p : Source.Parameters) (S : Source.SparseSystem)
    (hm : 2 ≤ S.nnz) (hpromise : Source.Promises p S) :
    let bits := binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊
    ((Logical.sourceCircuit S bits).size:ℝ) ≤
      6*(S.nnz:ℝ)*(8 + ((⌈p.conditionExponent⌉₊+⌈p.accuracyExponent⌉₊+2:ℕ):ℝ)*
        (1 + Real.log S.nnz/Real.log 2)) := by
  dsimp only
  have hd := Logical.sourceCircuit_size S
    (binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊)
    (Source.dimension_le_nnz S hpromise.1)
  have hdr : ((Logical.sourceCircuit S
      (binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊)).size:ℝ) ≤
      6*(S.nnz:ℝ)*((binaryCoefficientPrecision S.nnz ⌈p.conditionExponent⌉₊
        ⌈p.accuracyExponent⌉₊:ℝ)+1) := by exact_mod_cast hd
  have hp := binaryCoefficientPrecision_le_log S.nnz ⌈p.conditionExponent⌉₊
    ⌈p.accuracyExponent⌉₊ (by omega)
  exact hdr.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Maxwell.Realization
