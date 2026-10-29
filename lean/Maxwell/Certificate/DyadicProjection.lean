import Maxwell.Certificate.DyadicDivision

/-! Exact dyadic proposals for transverse Fourier projection. -/
namespace Maxwell.Certificate.DyadicRectangle

noncomputable def value (p : ℕ) (a : DyadicRectangle) : ℂ :=
  ⟨(a.re:ℝ)/(2:ℝ)^p, (a.im:ℝ)/(2:ℝ)^p⟩

theorem value_contains (p : ℕ) (a : DyadicRectangle) : a.Contains p (value p a) := by
  have hs : (2:ℝ)^p ≠ 0 := by positivity
  constructor <;> simp [value, hs]

/-- Subtract a contained value from an exact input; the reverse rectangle
uses no extra intermediate record. -/
theorem reverse_sub_contains {p : ℕ} {a b : DyadicRectangle} {z w : ℂ}
    (ha0 : a.radius = 0) (ha : a.Contains p z)
    (hw : (a.add b.neg).Contains p w) : b.Contains p (z-w) := by
  have hre : z.re*2^p=(a.re:ℝ) := by
    have h : |z.re*2^p-(a.re:ℝ)| ≤ 0 := by simpa only [ha0, Nat.cast_zero] using ha.1
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  have him : z.im*2^p=(a.im:ℝ) := by
    have h : |z.im*2^p-(a.im:ℝ)| ≤ 0 := by simpa only [ha0, Nat.cast_zero] using ha.2
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  constructor
  · have hh := hw.1
    change |w.re*2^p-((a.re + -b.re:ℤ):ℝ)| ≤ (a.radius+b.radius:ℕ) at hh
    simp only [Int.cast_add, Int.cast_neg, ha0, Nat.zero_add] at hh
    change |(z-w).re*2^p-(b.re:ℝ)| ≤ b.radius
    have he : (z-w).re*2^p-(b.re:ℝ) = -(w.re*2^p-(a.re+-b.re)) := by
      simp only [Complex.sub_re]
      nlinarith [hre]
    rw [he, abs_neg]
    exact hh
  · have hh := hw.2
    change |w.im*2^p-((a.im + -b.im:ℤ):ℝ)| ≤ (a.radius+b.radius:ℕ) at hh
    simp only [Int.cast_add, Int.cast_neg, ha0, Nat.zero_add] at hh
    change |(z-w).im*2^p-(b.im:ℝ)| ≤ b.radius
    have he : (z-w).im*2^p-(b.im:ℝ) = -(w.im*2^p-(a.im+-b.im)) := by
      simp only [Complex.sub_im]
      nlinarith [him]
    rw [he, abs_neg]
    exact hh

structure ProjectionProposal where
  dot : DyadicRectangle
  quotient : DyadicRectangle
  result : Fin 3 → DyadicRectangle

def projectionCheck (p : ℕ) (d raw : Fin 3 → DyadicRectangle)
    (lap : DyadicRectangle) (w : ProjectionProposal) : Bool :=
  decide (∀ i, (raw i).radius = 0) && dotCheck p p d raw w.dot &&
    divCheck p w.dot lap w.quotient && decide (∀ i,
      mulCheck p (d i).conjugate w.quotient ((raw i).add (w.result i).neg) = true)

theorem projectionCheck_sound {p : ℕ} {d raw : Fin 3 → DyadicRectangle}
    {lap : DyadicRectangle} {w : ProjectionProposal} {δ u : Fin 3 → ℂ} {l : ℝ}
    (h : projectionCheck p d raw lap w = true)
    (hd : ∀ i, (d i).Contains p (δ i)) (hu : ∀ i, (raw i).Contains p (u i))
    (hl : lap.Contains p (l:ℂ)) :
    ∀ i, (w.result i).Contains p (u i - star (δ i)*((∑ j, δ j*u j)/(l:ℂ))) := by
  simp only [projectionCheck, Bool.and_eq_true_iff] at h
  have he : ∀ i, (raw i).radius = 0 := of_decide_eq_true h.1.1.1
  have hm : ∀ i, mulCheck p (d i).conjugate w.quotient ((raw i).add (w.result i).neg) = true :=
    of_decide_eq_true h.2
  have hdot := dotCheck_sound h.1.1.2 hd hu
  have hdiv := divCheck_sound h.1.2 hdot hl
  intro i
  exact reverse_sub_contains (he i) (hu i)
    (mulCheck_sound (hm i) (conjugate_contains (hd i)) hdiv)

end Maxwell.Certificate.DyadicRectangle
