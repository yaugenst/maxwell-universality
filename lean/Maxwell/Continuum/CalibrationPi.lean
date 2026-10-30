import Maxwell.Continuum.CalibrationElementary
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! A finite rational Machin enclosure of pi at arbitrary dyadic
precision. Both arctangents are evaluated by their convergent series. -/

namespace Maxwell.Certificate.Elementary

def arctanTaylor (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1)^k*q^(2*k+1)/(2*k+1 : ℕ)

theorem arctan_term_bound {x : ℝ} (hx : |x| ≤ 1/2) (m : ℕ) :
    ‖(-1 : ℝ)^m*x^(2*m+1)/(2*m+1 : ℕ)‖ ≤ (1/2 : ℝ)^m := by
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    norm_natCast,Real.norm_eq_abs]
  calc
    _ ≤ |x|^(2*m+1) := div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ 2*m+1))
    _ ≤ (1/2 : ℝ)^(2*m+1) := pow_le_pow_left₀ (abs_nonneg _) hx _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem arctan_series_error {x : ℝ} (hx : |x| ≤ 1/2) (n : ℕ) :
    |Real.arctan x-∑ k ∈ Finset.range n, (-1 : ℝ)^k*x^(2*k+1)/(2*k+1 : ℕ)| ≤
      2*(1/2 : ℝ)^n := by
  let f : ℕ → ℝ := fun k => (-1 : ℝ)^k*x^(2*k+1)/(2*k+1 : ℕ)
  have hs : HasSum f (Real.arctan x) := Real.hasSum_arctan
    (by simpa only [Real.norm_eq_abs] using hx.trans_lt (by norm_num : (1/2 : ℝ) < 1))
  have hg : Summable (fun k : ℕ => (1/2 : ℝ)^k*(1/2 : ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_right _
  have hbound (k : ℕ) : ‖f (k+n)‖ ≤ (1/2 : ℝ)^k*(1/2 : ℝ)^n :=
    (arctan_term_bound hx (k+n)).trans_eq (pow_add _ _ _)
  have hsn : Summable (fun k => ‖f (k+n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hg
  have htail : Real.arctan x-∑ k ∈ Finset.range n, f k = ∑' k, f (k+n) := by
    rw [← hs.tsum_eq,← hs.summable.sum_add_tsum_nat_add n]
    ring
  change |Real.arctan x-∑ k ∈ Finset.range n, f k| ≤ _
  rw [htail,← Real.norm_eq_abs]
  calc
    _ ≤ ∑' k, ‖f (k+n)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' k, (1/2 : ℝ)^k*(1/2 : ℝ)^n := hsn.tsum_le_tsum hbound hg
    _ = 2*(1/2 : ℝ)^n := by
      rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
      norm_num

theorem arctanTaylor_error (q : ℚ) (n : ℕ) (hq : |q| ≤ 1/2) :
    |Real.arctan (q : ℝ)-(arctanTaylor q n : ℝ)| ≤ 2*(1/2 : ℝ)^n := by
  have hx : |(q : ℝ)| ≤ 1/2 := by
    have h : ((|q| : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    simpa using h
  simpa only [arctanTaylor,Rat.cast_sum,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_neg,Rat.cast_one,Rat.cast_natCast] using arctan_series_error hx n

def piApprox (N : ℕ) : Ball :=
  ⟨16*arctanTaylor (1/5) (N+6)-4*arctanTaylor (1/239) (N+6),
    (1/2)^N,by positivity⟩

theorem piApprox_contains (N : ℕ) : (piApprox N).Contains Real.pi := by
  have h5 := arctanTaylor_error (1/5) (N+6) (by norm_num)
  have h239 := arctanTaylor_error (1/239) (N+6) (by norm_num)
  have hm : Real.pi = 16*Real.arctan ((1/5 : ℚ) : ℝ)-
      4*Real.arctan ((1/239 : ℚ) : ℝ) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num at h ⊢
    linarith
  unfold Ball.Contains piApprox
  rw [hm]
  push_cast
  have he : 16*Real.arctan ((1/5 : ℚ) : ℝ)-4*Real.arctan ((1/239 : ℚ) : ℝ)-
      (16*(arctanTaylor (1/5) (N+6) : ℝ)-4*(arctanTaylor (1/239) (N+6) : ℝ)) =
      16*(Real.arctan ((1/5 : ℚ) : ℝ)-(arctanTaylor (1/5) (N+6) : ℝ))-
      4*(Real.arctan ((1/239 : ℚ) : ℝ)-(arctanTaylor (1/239) (N+6) : ℝ)) := by ring
  push_cast at he h5 h239
  rw [he]
  calc
    _ ≤ |16*(Real.arctan (1/5)-(arctanTaylor (1/5) (N+6) : ℝ))|+
        |4*(Real.arctan (1/239)-(arctanTaylor (1/239) (N+6) : ℝ))| := abs_sub _ _
    _ ≤ 16*(2*(1/2 : ℝ)^(N+6))+4*(2*(1/2 : ℝ)^(N+6)) := by
      rw [abs_mul,abs_mul]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 16),
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact add_le_add (mul_le_mul_of_nonneg_left h5 (by norm_num))
        (mul_le_mul_of_nonneg_left h239 (by norm_num))
    _ ≤ (1/2 : ℝ)^N := by
      rw [pow_add]
      norm_num
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) N]

theorem piApprox_radius (N : ℕ) : (piApprox N).radius = (1/2 : ℚ)^N := rfl

#print axioms piApprox_contains

end Maxwell.Certificate.Elementary
