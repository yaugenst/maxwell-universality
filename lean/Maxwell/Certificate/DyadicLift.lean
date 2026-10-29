import Maxwell.Certificate.DyadicRectangle

namespace Maxwell.Certificate.DyadicRectangle

/-- An exact change of dyadic precision. All three integer channels scale. -/
def liftPrecision (q : ℕ) (a : DyadicRectangle) : DyadicRectangle :=
  ⟨a.re * 2^q, a.im * 2^q, a.radius * 2^q⟩

theorem liftPrecision_contains_iff (p q : ℕ) (a : DyadicRectangle) (z : ℂ) :
    (a.liftPrecision q).Contains (p+q) z ↔ a.Contains p z := by
  have hq : (0 : ℝ) < 2^q := by positivity
  have he (x : ℝ) (v : ℤ) :
      |x * (2:ℝ)^(p+q) - (v * (2:ℤ)^q : ℤ)| =
        |x * (2:ℝ)^p - v| * (2:ℝ)^q := by
    push_cast
    rw [pow_add, ← mul_assoc, ← sub_mul, abs_mul, abs_of_pos hq]
  simp only [Contains, liftPrecision, he, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact and_congr (mul_le_mul_iff_left₀ hq) (mul_le_mul_iff_left₀ hq)

theorem liftPrecision_contains {p q : ℕ} {a : DyadicRectangle} {z : ℂ}
    (h : a.Contains p z) : (a.liftPrecision q).Contains (p+q) z :=
  (liftPrecision_contains_iff p q a z).mpr h

theorem lift48to52_contains_iff (a : DyadicRectangle) (z : ℂ) :
    (⟨a.re*16,a.im*16,a.radius*16⟩ : DyadicRectangle).Contains 52 z ↔
      a.Contains 48 z := by
  convert liftPrecision_contains_iff 48 4 a z using 1
  norm_num [liftPrecision]

end Maxwell.Certificate.DyadicRectangle
