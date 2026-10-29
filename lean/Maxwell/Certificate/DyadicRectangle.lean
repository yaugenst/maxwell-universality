import Maxwell.Certificate.IntervalLinear

/-! Integer-only predicates for outward-rounded dyadic rectangle arithmetic.
The input records have no machine-word bound; Lean integers are exact. -/
namespace Maxwell.Certificate

structure DyadicRectangle where
  re : ℤ
  im : ℤ
  radius : ℕ
deriving DecidableEq

namespace DyadicRectangle

def toRectangle (p : ℕ) (a : DyadicRectangle) : ComplexRectangle :=
  ⟨⟨a.re / (2 : ℚ)^p, a.radius / (2 : ℚ)^p, by positivity⟩,
   ⟨a.im / (2 : ℚ)^p, a.radius / (2 : ℚ)^p, by positivity⟩⟩

def Contains (p : ℕ) (a : DyadicRectangle) (z : ℂ) : Prop :=
  |z.re * (2 : ℝ)^p - a.re| ≤ a.radius ∧
  |z.im * (2 : ℝ)^p - a.im| ≤ a.radius

theorem contains_iff (p : ℕ) (a : DyadicRectangle) (z : ℂ) :
    a.Contains p z ↔ (a.toRectangle p).Contains z := by
  have hp : (0 : ℝ) < 2^p := by positivity
  have he (x : ℝ) (m : ℤ) : x - (m : ℝ) / 2^p = (x*2^p-m)/2^p := by
    field_simp
  simp only [Contains, ComplexRectangle.Contains, toRectangle, Ball.Contains,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat,
    he, abs_div, abs_of_pos hp, div_le_div_iff_of_pos_right hp]

def subsetCheck (a b : DyadicRectangle) : Bool :=
  decide (|a.re-b.re| + (a.radius : ℤ) ≤ b.radius ∧
    |a.im-b.im| + (a.radius : ℤ) ≤ b.radius)

theorem subsetCheck_sound {p : ℕ} {a b : DyadicRectangle}
    (h : subsetCheck a b = true) {z : ℂ} (ha : a.Contains p z) : b.Contains p z := by
  have hh : |a.re-b.re| + (a.radius : ℤ) ≤ b.radius ∧
      |a.im-b.im| + (a.radius : ℤ) ≤ b.radius := of_decide_eq_true h
  have hr : |(a.re : ℝ)-b.re| + a.radius ≤ b.radius := by exact_mod_cast hh.1
  have hi : |(a.im : ℝ)-b.im| + a.radius ≤ b.radius := by exact_mod_cast hh.2
  constructor
  · calc
      |z.re * 2^p - (b.re : ℝ)| = |(z.re*2^p-a.re)+(a.re-b.re)| := by ring_nf
      _ ≤ |z.re*2^p-a.re|+|(a.re : ℝ)-b.re| := abs_add_le _ _
      _ ≤ b.radius := by linarith [ha.1]
  · calc
      |z.im * 2^p - (b.im : ℝ)| = |(z.im*2^p-a.im)+(a.im-b.im)| := by ring_nf
      _ ≤ |z.im*2^p-a.im|+|(a.im : ℝ)-b.im| := abs_add_le _ _
      _ ≤ b.radius := by linarith [ha.2]

def add (a b : DyadicRectangle) : DyadicRectangle :=
  ⟨a.re+b.re,a.im+b.im,a.radius+b.radius⟩

def neg (a : DyadicRectangle) : DyadicRectangle := ⟨-a.re,-a.im,a.radius⟩

def conjugate (a : DyadicRectangle) : DyadicRectangle := ⟨a.re,-a.im,a.radius⟩

theorem add_contains {p : ℕ} {a b : DyadicRectangle} {z w : ℂ}
    (ha : a.Contains p z) (hb : b.Contains p w) : (a.add b).Contains p (z+w) := by
  constructor
  · have h := (abs_add_le (z.re*2^p-a.re) (w.re*2^p-b.re)).trans (add_le_add ha.1 hb.1)
    convert h using 1 <;> simp [add, Complex.add_re]
    congr 1
    ring
  · have h := (abs_add_le (z.im*2^p-a.im) (w.im*2^p-b.im)).trans (add_le_add ha.2 hb.2)
    convert h using 1 <;> simp [add, Complex.add_im]
    congr 1
    ring

theorem neg_contains {p : ℕ} {a : DyadicRectangle} {z : ℂ}
    (ha : a.Contains p z) : a.neg.Contains p (-z) := by
  constructor
  · simpa only [neg, Complex.neg_re, Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm] using ha.1
  · simpa only [neg, Complex.neg_im, Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm] using ha.2

theorem conjugate_contains {p : ℕ} {a : DyadicRectangle} {z : ℂ}
    (ha : a.Contains p z) : a.conjugate.Contains p (star z) := by
  constructor
  · exact ha.1
  · simpa only [conjugate, Complex.star_def, Complex.conj_im, Int.cast_neg, neg_mul, neg_sub_neg, abs_sub_comm] using ha.2

def mulError (a b : DyadicRectangle) : ℤ :=
  (|a.re|+|a.im|)*b.radius + (|b.re|+|b.im|)*a.radius + 2*a.radius*b.radius

def mulCheck (p : ℕ) (a b c : DyadicRectangle) : Bool :=
  let s : ℤ := 2^p
  decide (|a.re*b.re-a.im*b.im-c.re*s|+mulError a b ≤ c.radius*s ∧
    |a.re*b.im+a.im*b.re-c.im*s|+mulError a b ≤ c.radius*s)

private theorem real_mul_error (x u a b r s : ℝ) (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hx : |x-a| ≤ r) (hu : |u-b| ≤ s) :
    |x*u-a*b| ≤ |a| * s+|b| * r+r*s := by
  calc
    |x*u-a*b| = |a*(u-b)+b*(x-a)+(x-a)*(u-b)| := by congr 1; ring
    _ ≤ |a*(u-b)| + |b*(x-a)| + |(x-a)*(u-b)| := abs_add_three _ _ _
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
        (mul_le_mul hx hu (abs_nonneg _) hr)

theorem mulCheck_sound {p : ℕ} {a b c : DyadicRectangle}
    (h : mulCheck p a b c = true) {z w : ℂ}
    (ha : a.Contains p z) (hb : b.Contains p w) : c.Contains p (z*w) := by
  have hs : (0 : ℝ) < 2^p := by positivity
  have hscale (x : ℝ) : |x| * 2^p = |x*2^p| := by rw [abs_mul, abs_of_pos hs]
  have hh : |a.re*b.re-a.im*b.im-c.re*(2:ℤ)^p|+mulError a b ≤ c.radius*(2:ℤ)^p ∧
      |a.re*b.im+a.im*b.re-c.im*(2:ℤ)^p|+mulError a b ≤ c.radius*(2:ℤ)^p := of_decide_eq_true h
  have h1 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.1 hb.1
  have h2 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.2 hb.2
  have h3 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.1 hb.2
  have h4 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.2 hb.1
  have hr : |(a.re:ℝ)*b.re-a.im*b.im-c.re*(2:ℝ)^p|+
      (|a.re|+|a.im|)*(b.radius:ℝ)+(|b.re|+|b.im|)*(a.radius:ℝ)+2*a.radius*b.radius ≤ c.radius*(2:ℝ)^p := by
    have hh1 := hh.1
    unfold mulError at hh1
    exact_mod_cast (by simpa only [add_assoc] using hh1 :
      |a.re*b.re-a.im*b.im-c.re*(2:ℤ)^p|+
      (|a.re|+|a.im|)*(b.radius:ℤ)+(|b.re|+|b.im|)*(a.radius:ℤ)+
      2*(a.radius:ℤ)*b.radius ≤ (c.radius:ℤ)*(2:ℤ)^p)
  have hi : |(a.re:ℝ)*b.im+a.im*b.re-c.im*(2:ℝ)^p|+
      (|a.re|+|a.im|)*(b.radius:ℝ)+(|b.re|+|b.im|)*(a.radius:ℝ)+2*a.radius*b.radius ≤ c.radius*(2:ℝ)^p := by
    have hh2 := hh.2
    unfold mulError at hh2
    exact_mod_cast (by simpa only [add_assoc] using hh2 :
      |a.re*b.im+a.im*b.re-c.im*(2:ℤ)^p|+
      (|a.re|+|a.im|)*(b.radius:ℤ)+(|b.re|+|b.im|)*(a.radius:ℤ)+
      2*(a.radius:ℤ)*b.radius ≤ (c.radius:ℤ)*(2:ℤ)^p)
  push_cast at hr hi
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [hscale]
    have he : ((z*w).re*2^p-(c.re:ℝ))*2^p =
        (z.re*2^p*(w.re*2^p)-a.re*b.re) - (z.im*2^p*(w.im*2^p)-a.im*b.im) +
          (a.re*b.re-a.im*b.im-c.re*2^p) := by simp [Complex.mul_re]; ring
    rw [he]
    have ht := abs_add_le ((z.re*2^p*(w.re*2^p)-a.re*b.re) -
      (z.im*2^p*(w.im*2^p)-a.im*b.im)) ((a.re:ℝ)*b.re-a.im*b.im-c.re*2^p)
    have ht2 := abs_add_le (z.re*2^p*(w.re*2^p)-a.re*b.re) (-(z.im*2^p*(w.im*2^p)-a.im*b.im))
    simp only [abs_neg, ← sub_eq_add_neg] at ht2
    nlinarith
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [hscale]
    have he : ((z*w).im*2^p-(c.im:ℝ))*2^p =
        (z.re*2^p*(w.im*2^p)-a.re*b.im) + (z.im*2^p*(w.re*2^p)-a.im*b.re) +
          (a.re*b.im+a.im*b.re-c.im*2^p) := by simp [Complex.mul_im]; ring
    rw [he]
    have ht := abs_add_three (z.re*2^p*(w.im*2^p)-a.re*b.im)
      (z.im*2^p*(w.re*2^p)-a.im*b.re) ((a.re:ℝ)*b.im+a.im*b.re-c.im*2^p)
    nlinarith


/-- Unrounded product: input precision `p,q` becomes precision `p+q`. -/
def mulExact (a b : DyadicRectangle) : DyadicRectangle :=
  ⟨a.re*b.re-a.im*b.im, a.re*b.im+a.im*b.re, (mulError a b).toNat⟩

theorem mulError_nonneg (a b : DyadicRectangle) : 0 ≤ mulError a b := by
  unfold mulError
  positivity

theorem mulExact_contains {p q : ℕ} {a b : DyadicRectangle} {z w : ℂ}
    (ha : a.Contains p z) (hb : b.Contains q w) :
    (mulExact a b).Contains (p+q) (z*w) := by
  have h1 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.1 hb.1
  have h2 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.2 hb.2
  have h3 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.1 hb.2
  have h4 := real_mul_error _ _ _ _ _ _ (Nat.cast_nonneg a.radius) (Nat.cast_nonneg b.radius) ha.2 hb.1
  have hr : ((mulError a b).toNat : ℝ) =
      (|(a.re:ℝ)|+|(a.im:ℝ)|)*b.radius+
      (|(b.re:ℝ)|+|(b.im:ℝ)|)*a.radius+2*a.radius*b.radius := by
    have he : ((mulError a b).toNat : ℝ) = (mulError a b : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (mulError_nonneg a b)
    rw [he]
    simp [mulError]
  constructor
  · change |(z*w).re*2^(p+q)-((a.re*b.re-a.im*b.im:ℤ):ℝ)| ≤ _
    change _ ≤ ((mulError a b).toNat : ℝ)
    rw [hr]
    push_cast
    have he : (z*w).re*2^(p+q)-((a.re:ℝ)*b.re-a.im*b.im) =
        (z.re*2^p*(w.re*2^q)-a.re*b.re) + -(z.im*2^p*(w.im*2^q)-a.im*b.im) := by
      simp only [Complex.mul_re, pow_add]
      ring
    rw [he]
    have ht := abs_add_le (z.re*2^p*(w.re*2^q)-a.re*b.re)
      (-(z.im*2^p*(w.im*2^q)-a.im*b.im))
    rw [abs_neg] at ht
    nlinarith
  · change |(z*w).im*2^(p+q)-((a.re*b.im+a.im*b.re:ℤ):ℝ)| ≤ _
    change _ ≤ ((mulError a b).toNat : ℝ)
    rw [hr]
    push_cast
    have he : (z*w).im*2^(p+q)-((a.re:ℝ)*b.im+a.im*b.re) =
        (z.re*2^p*(w.im*2^q)-a.re*b.im) + (z.im*2^p*(w.re*2^q)-a.im*b.re) := by
      simp only [Complex.mul_im, pow_add]
      ring
    rw [he]
    have ht := abs_add_le (z.re*2^p*(w.im*2^q)-a.re*b.im)
      (z.im*2^p*(w.re*2^q)-a.im*b.re)
    nlinarith

def zero : DyadicRectangle := ⟨0,0,0⟩

theorem zero_contains (p : ℕ) : zero.Contains p 0 := by simp [Contains, zero]

def sum : {n : ℕ} → (Fin n → DyadicRectangle) → DyadicRectangle
  | 0, _ => zero
  | _+1, a => (a 0).add (sum fun i => a i.succ)

theorem sum_contains {n p : ℕ} {a : Fin n → DyadicRectangle} {z : Fin n → ℂ}
    (h : ∀ i, (a i).Contains p (z i)) : (sum a).Contains p (∑ i, z i) := by
  induction n with
  | zero => simpa [sum] using zero_contains p
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      exact add_contains (h 0) (ih fun i => h i.succ)

/-- Reduce a dyadic scale from `p+q` to `p`, checking outward rounding. -/
def rescaleCheck (_p q : ℕ) (a b : DyadicRectangle) : Bool :=
  let s : ℤ := 2^q
  decide (|a.re-b.re*s|+(a.radius:ℤ) ≤ b.radius*s ∧
    |a.im-b.im*s|+(a.radius:ℤ) ≤ b.radius*s)

theorem rescaleCheck_sound {p q : ℕ} {a b : DyadicRectangle} {z : ℂ}
    (h : rescaleCheck p q a b = true) (ha : a.Contains (p+q) z) : b.Contains p z := by
  have hs : (0:ℝ) < 2^q := by positivity
  have hh : |a.re-b.re*(2:ℤ)^q|+(a.radius:ℤ) ≤ b.radius*(2:ℤ)^q ∧
      |a.im-b.im*(2:ℤ)^q|+(a.radius:ℤ) ≤ b.radius*(2:ℤ)^q := of_decide_eq_true h
  have hr : |(a.re:ℝ)-b.re*(2:ℝ)^q|+a.radius ≤ b.radius*(2:ℝ)^q := by exact_mod_cast hh.1
  have hi : |(a.im:ℝ)-b.im*(2:ℝ)^q|+a.radius ≤ b.radius*(2:ℝ)^q := by exact_mod_cast hh.2
  constructor
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]
    have he : (z.re*2^p-(b.re:ℝ))*2^q =
        (z.re*2^(p+q)-a.re)+(a.re-b.re*2^q) := by rw [pow_add]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [ha.1])
  · apply (mul_le_mul_iff_of_pos_right hs).mp
    rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]
    have he : (z.im*2^p-(b.im:ℝ))*2^q =
        (z.im*2^(p+q)-a.im)+(a.im-b.im*2^q) := by rw [pow_add]; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [ha.2])

/-- A single integer check for an entire matrix row, with one final rounding. -/
def dotCheck {n : ℕ} (p q : ℕ) (a b : Fin n → DyadicRectangle)
    (c : DyadicRectangle) : Bool := rescaleCheck p q (sum fun i => mulExact (a i) (b i)) c

theorem dotCheck_sound {n p q : ℕ} {a b : Fin n → DyadicRectangle}
    {c : DyadicRectangle} {z w : Fin n → ℂ}
    (h : dotCheck p q a b c = true)
    (ha : ∀ i, (a i).Contains p (z i)) (hb : ∀ i, (b i).Contains q (w i)) :
    c.Contains p (∑ i, z i*w i) :=
  rescaleCheck_sound h (sum_contains fun i => mulExact_contains (ha i) (hb i))

end DyadicRectangle
end Maxwell.Certificate
