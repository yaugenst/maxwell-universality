import Maxwell.Certificate.DyadicKernelRows

namespace Maxwell.Certificate.DyadicRectangle

/-- The same integers represent a value divided by a dyadic factor when the
interpretation precision is increased by that factor's exponent. -/
theorem contains_div_pow {p r : ℕ} {a : DyadicRectangle} {z : ℂ}
    (h : a.Contains p z) : a.Contains (p+r) (z / (2 : ℂ)^r) := by
  have hs : (2 : ℝ)^r ≠ 0 := by positivity
  have he : (2 : ℂ)^r = Complex.ofReal ((2 : ℝ)^r) := by norm_cast
  rw [he]
  constructor
  · change |(z / Complex.ofReal ((2 : ℝ)^r)).re * 2^(p+r) - a.re| ≤ a.radius
    rw [Complex.div_ofReal_re, pow_add]
    convert h.1 using 1
    congr 1
    field_simp
  · change |(z / Complex.ofReal ((2 : ℝ)^r)).im * 2^(p+r) - a.im| ≤ a.radius
    rw [Complex.div_ofReal_im, pow_add]
    convert h.2 using 1
    congr 1
    field_simp

theorem scaledDotCheck_sound {n p q r : ℕ} {a b : Fin n → DyadicRectangle}
    {c : DyadicRectangle} {z w : Fin n → ℂ}
    (h : dotCheck p (q+r) a b c = true)
    (ha : ∀ i, (a i).Contains p (z i)) (hb : ∀ i, (b i).Contains q (w i)) :
    c.Contains p ((∑ i, z i*w i)/(2:ℂ)^r) := by
  apply rescaleCheck_sound h
  simpa only [Nat.add_assoc] using
    (contains_div_pow (r := r) (sum_contains fun i => mulExact_contains (ha i) (hb i)))

end Maxwell.Certificate.DyadicRectangle
