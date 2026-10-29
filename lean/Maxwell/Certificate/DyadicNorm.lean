import Maxwell.Certificate.DyadicRectangle

/-! Integer upper bounds for complex squared norms and finite sums. -/
namespace Maxwell.Certificate.DyadicRectangle

def normSqUpper (a : DyadicRectangle) : ℤ :=
  (|a.re| + a.radius)^2 + (|a.im| + a.radius)^2

theorem normSqUpper_nonneg (a : DyadicRectangle) : 0 ≤ normSqUpper a := by
  unfold normSqUpper
  positivity

theorem norm_sq_scaled_le {p : ℕ} {a : DyadicRectangle} {z : ℂ}
    (ha : a.Contains p z) : ‖z‖^2 * (2:ℝ)^(2*p) ≤ (normSqUpper a : ℝ) := by
  have hchannel (x : ℝ) (m : ℤ) (h : |x*2^p-m| ≤ a.radius) :
      (x*2^p)^2 ≤ (|(m:ℝ)| + a.radius)^2 := by
    have hh : |x*2^p| ≤ |(m:ℝ)| + a.radius := by
      calc
        |x*2^p| = |(x*2^p-m)+m| := by congr 1; ring
        _ ≤ |x*2^p-m| + |(m:ℝ)| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hs := mul_self_le_mul_self (abs_nonneg _) hh
    simpa only [← sq, sq_abs] using hs
  have hr := hchannel z.re a.re ha.1
  have hi := hchannel z.im a.im ha.2
  have hn : ‖z‖^2 = z.re^2+z.im^2 := by
    simpa only [Complex.normSq_apply, ← sq] using Complex.sq_norm z
  rw [hn]
  have hp : (2:ℝ)^(2*p) = (2^p)^2 := by rw [mul_comm 2 p, pow_mul]
  rw [hp]
  simp only [normSqUpper, Int.cast_add, Int.cast_pow, Int.cast_abs, Int.cast_natCast]
  nlinarith

theorem sum_norm_sq_le {ι : Type*} [Fintype ι] {p : ℕ}
    {a : ι → DyadicRectangle} {z : ι → ℂ} {U : ℤ}
    (ha : ∀ i, (a i).Contains p (z i))
    (hU : ∑ i, normSqUpper (a i) ≤ U) :
    ∑ i, ‖z i‖^2 ≤ (U : ℝ) / (2:ℝ)^(2*p) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^(2*p))).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ i, (normSqUpper (a i) : ℝ) :=
      Finset.sum_le_sum fun i _ => norm_sq_scaled_le (ha i)
    _ ≤ U := by exact_mod_cast hU

end Maxwell.Certificate.DyadicRectangle
