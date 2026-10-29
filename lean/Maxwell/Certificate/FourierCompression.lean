import Maxwell.Certificate.FourierCoercivity

/-! Exact low-frequency compression with a certified omitted-frequency
error. Only the high parts of the trial field and its actual operator
action enter the error bound. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

theorem inner_frequencyRestriction_split (support : Finset Frequency)
    (x y : FourierSpace) :
    inner ℂ x y =
      inner ℂ (frequencyRestriction support x) (frequencyRestriction support y) +
      inner ℂ (frequencyRestriction supportᶜ x) (frequencyRestriction supportᶜ y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e.2 ∈ support <;> simp [frequencyRestriction, he]

/-- The omitted part of a compression entry is bounded by the product
of the actual omitted field norm and omitted action norm. -/
theorem frequency_compression_error (support : Finset Frequency)
    (x y : FourierSpace) :
    |(inner ℂ x y).re -
      (inner ℂ (frequencyRestriction support x) (frequencyRestriction support y)).re| ≤
      ‖frequencyRestriction supportᶜ x‖ * ‖frequencyRestriction supportᶜ y‖ := by
  rw [inner_frequencyRestriction_split support x y, Complex.add_re, add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

theorem frequency_trial_compression_error
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (support : Finset Frequency) (A : FourierSpace →ₗ[ℂ] FourierSpace)
    (F : P →ₗ[ℂ] FourierSpace) (rF rA : ℝ)
    (hF : ∀ p, ‖frequencyRestriction supportᶜ (F p)‖ ≤ rF * ‖p‖)
    (hA : ∀ p, ‖frequencyRestriction supportᶜ (A (F p))‖ ≤ rA * ‖p‖)
    (p : P) :
    |(inner ℂ (F p) (A (F p))).re -
      (inner ℂ (frequencyRestriction support (F p))
        (frequencyRestriction support (A (F p)))).re| ≤ rF * rA * ‖p‖ ^ 2 := by
  calc
    _ ≤ ‖frequencyRestriction supportᶜ (F p)‖ *
        ‖frequencyRestriction supportᶜ (A (F p))‖ := frequency_compression_error _ _ _
    _ ≤ (rF * ‖p‖) * (rA * ‖p‖) :=
      mul_le_mul (hF p) (hA p) (norm_nonneg _) ((norm_nonneg _).trans (hF p))
    _ = _ := by ring

/-- A low-frequency lower form bound transfers to the full actual form
after subtracting the proved high-frequency compression error. -/
theorem frequency_compression_lower
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (support : Finset Frequency) (A : FourierSpace →ₗ[ℂ] FourierSpace)
    (F : P →ₗ[ℂ] FourierSpace) (a rF rA : ℝ)
    (hF : ∀ p, ‖frequencyRestriction supportᶜ (F p)‖ ≤ rF * ‖p‖)
    (hA : ∀ p, ‖frequencyRestriction supportᶜ (A (F p))‖ ≤ rA * ‖p‖)
    (hlo : ∀ p, a * ‖p‖ ^ 2 ≤
      (inner ℂ (frequencyRestriction support (F p))
        (frequencyRestriction support (A (F p)))).re)
    (p : P) : (a - rF * rA) * ‖p‖ ^ 2 ≤ (inner ℂ (F p) (A (F p))).re := by
  have h := (abs_le.mp (frequency_trial_compression_error support A F rF rA hF hA p)).1
  nlinarith [hlo p]

theorem frequency_compression_upper
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (support : Finset Frequency) (A : FourierSpace →ₗ[ℂ] FourierSpace)
    (F : P →ₗ[ℂ] FourierSpace) (a rF rA : ℝ)
    (hF : ∀ p, ‖frequencyRestriction supportᶜ (F p)‖ ≤ rF * ‖p‖)
    (hA : ∀ p, ‖frequencyRestriction supportᶜ (A (F p))‖ ≤ rA * ‖p‖)
    (hlo : ∀ p,
      (inner ℂ (frequencyRestriction support (F p))
        (frequencyRestriction support (A (F p)))).re ≤ a * ‖p‖ ^ 2)
    (p : P) : (inner ℂ (F p) (A (F p))).re ≤ (a + rF * rA) * ‖p‖ ^ 2 := by
  have h := (abs_le.mp (frequency_trial_compression_error support A F rF rA hF hA p)).2
  nlinarith [hlo p]

end Maxwell.Certificate.FourierBinding
