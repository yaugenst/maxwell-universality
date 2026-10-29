import Maxwell.Cost.WeightedSource.Compute
import Maxwell.Cost.ModeRead.Value
import Maxwell.Green.SourceRoundingPrecision

namespace Maxwell.Cost.WeightedSource
open Maxwell.Defect.DyadicSqrt.Integer

/-- The stored signed channels use their original common denominator. -/
def represented {n : ℕ} (d : ModeRead.Data n) (i : Fin n) : ℚ :=
  ((d.value i 0 : ℚ)-d.value i 1)/d.denominator

theorem round_value (negative : Bool) (m d a q : ℕ) :
    Round.value negative m d a q =
      ((a : ℚ)/q)*RationalCanonical.value negative m d := by
  cases negative <;> simp [Round.value,RationalCanonical.value,div_eq_mul_inv] <;> ring

theorem inputValue_fraction {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k : ℕ) :
    Compute.inputValue d i A D k = ((lowerNum A D k : ℚ)/(2^k : ℕ))*represented d i := by
  rw [Compute.inputValue,round_value,ModeRead.Signed.scalar_value]
  rfl

theorem inputValue_bound {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k : ℕ)
    (h : |represented d i| ≤ 1) : |Compute.inputValue d i A D k| ≤ 1 := by
  rw [inputValue_fraction,abs_mul]
  have hlo : (0 : ℚ) ≤ (lowerNum A D k : ℚ)/(2^k : ℕ) := by positivity
  have hhi : (lowerNum A D k : ℚ)/(2^k : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (lowerNum_lt_pow_two A D k).le
  rw [abs_of_nonneg hlo]
  exact (mul_le_mul hhi h (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem inputValue_weight {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D b : ℕ)
    (hD : 0<D) : Compute.inputValue d i A D (2*b+5) =
      Maxwell.Defect.DyadicSqrt.weight ((A : ℚ)/D) (b+2)*represented d i := by
  rw [inputValue_fraction,Weight.weight_binding A D b hD]

/-- Exact agreement with the paper's shared weighted and rounded source.
Only the coordinate representation and fixed literal weight are premises. -/
theorem rounded_value {n : ℕ} (d : ModeRead.Data n) (i : Fin n)
    (W : Fin n → ℚ) (q : ℕ → Fin n → ℚ) (A D b : ℕ) (hD : 0<D)
    (hW : (A : ℚ)/D=W i) (hq : represented d i=q (b+2) i) :
    ((Compute.numerator d i A D (2*b+5) (b+Nat.clog 2 (n+1)) : ℤ) : ℚ)/
      (2^(b+Nat.clog 2 (n+1)) : ℕ) =
        Maxwell.Defect.SourceRounding.roundedWeightedVector W q b i := by
  rw [Maxwell.Defect.SourceRounding.roundedWeightedVector_nearest]
  unfold Compute.numerator
  rw [inputValue_weight d i A D b hD,hW,hq]
  simp only [Maxwell.Dyadic.value,Nat.cast_pow,Nat.cast_ofNat]

theorem channel_value {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (A D k p : ℕ) :
    ((Split.positive (Compute.numerator d i A D k p) : ℚ)-
      (Split.negative (Compute.numerator d i A D k p) : ℚ))/(2^p : ℕ) =
        ((Compute.numerator d i A D k p : ℤ) : ℚ)/(2^p : ℕ) := by
  congr 1
  exact_mod_cast Split.value (Compute.numerator d i A D k p)

end Maxwell.Cost.WeightedSource
