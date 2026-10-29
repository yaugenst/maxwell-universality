import Maxwell.Logical.CachedNormalization

/-! A maximum scan keeps one original numerator/denominator pair. Therefore
normalization introduces no fraction growth during the maximum computation. -/

namespace Maxwell.Cost.MagnitudeMax
open Maxwell.Logical.Normalization

abbrev Pair := ℕ × ℕ

def value (p : Pair) : ℚ := (p.1 : ℚ) / p.2

def ofRational (q : ℚ) : Pair := (q.num.natAbs, q.den)

theorem ofRational_value (q : ℚ) : value (ofRational q) = |q| := by
  conv_rhs => rw [← q.num_div_den]
  simp [value, ofRational, abs_div]

def select (current : Pair) (q : ℚ) : Pair :=
  if value current < |q| then ofRational q else current

theorem select_value (current : Pair) (q : ℚ) :
    value (select current q) = max (value current) |q| := by
  unfold select
  split_ifs with h
  · rw [ofRational_value, max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]

def scan : Pair → List ℚ → Pair
  | current, [] => current
  | current, q :: qs => scan (select current q) qs

theorem scan_value (current : Pair) (qs : List ℚ) :
    value (scan current qs) = max (value current) (magnitudeMax qs) := by
  induction qs generalizing current with
  | nil =>
      have h0 : (0 : ℚ) ≤ value current := by unfold value; positivity
      simpa only [scan, magnitudeMax] using (max_eq_left h0).symm
  | cons q qs ih => rw [scan, ih, select_value, magnitudeMax, max_assoc]

theorem scan_selected (current : Pair) (qs : List ℚ) :
    scan current qs = current ∨ ∃ q ∈ qs, scan current qs = ofRational q := by
  induction qs generalizing current with
  | nil => exact Or.inl rfl
  | cons q qs ih =>
      rcases ih (select current q) with h | ⟨r, hr, he⟩
      · have hs : select current q = current ∨ select current q = ofRational q := by
          unfold select
          split_ifs <;> simp
        rcases hs with hs | hs
        · exact Or.inl (h.trans hs)
        · exact Or.inr ⟨q, List.mem_cons_self, h.trans hs⟩
      · exact Or.inr ⟨r, List.mem_cons_of_mem q hr, he⟩

def maximum (qs : List ℚ) : Pair := scan (0, 1) qs

theorem maximum_value (qs : List ℚ) : value (maximum qs) = magnitudeMax qs := by
  rw [maximum, scan_value]
  simp only [value, Nat.cast_zero, Nat.cast_one, zero_div]
  exact max_eq_right (magnitudeMax_nonneg qs)

theorem maximum_selected (qs : List ℚ) :
    maximum qs = (0, 1) ∨ ∃ q ∈ qs, maximum qs = (q.num.natAbs, q.den) := scan_selected _ qs

theorem maximum_width (qs : List ℚ) (numeratorBits denominatorBits : ℕ)
    (hden : 1 ≤ denominatorBits)
    (hnum : ∀ q ∈ qs, q.num.natAbs.bits.length ≤ numeratorBits)
    (hdenom : ∀ q ∈ qs, q.den.bits.length ≤ denominatorBits) :
    (maximum qs).1.bits.length ≤ numeratorBits ∧
      (maximum qs).2.bits.length ≤ denominatorBits := by
  rcases maximum_selected qs with h | ⟨q, hq, h⟩
  · simp [h, hden]
  · rw [h]
    exact ⟨hnum q hq, hdenom q hq⟩

end Maxwell.Cost.MagnitudeMax
