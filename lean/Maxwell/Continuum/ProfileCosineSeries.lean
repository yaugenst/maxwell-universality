import Maxwell.Continuum.ProfileFourierSeries

/-! Real cosine reconstruction by symmetric pairing of the actual Fourier series. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

def cosineCoefficient (j : ℕ) : ℝ :=
  if j = 0 then (angularCoefficient 0 0).re
  else (angularCoefficient 0 (j : ℤ)).re+(angularCoefficient 0 (-(j : ℤ))).re

theorem mode_re (n : ℤ) (φ : ℝ) : (mode n φ).re = Real.cos ((n : ℝ)*φ) := by
  have he : Complex.I*(n : ℂ)*(φ : ℂ) = (((n : ℝ)*φ : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [mode, he, Complex.exp_ofReal_mul_I_re]

theorem mode_im (n : ℤ) (φ : ℝ) : (mode n φ).im = Real.sin ((n : ℝ)*φ) := by
  have he : Complex.I*(n : ℂ)*(φ : ℂ) = (((n : ℝ)*φ : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [mode, he, Complex.exp_ofReal_mul_I_im]

theorem mode_pair_real (n : ℤ) (φ : ℝ) (c : ℂ) :
    ((mode n φ*c+mode n (-φ)*c)/2).re = c.re*Real.cos ((n : ℝ)*φ) := by
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.add_re, Complex.add_im,
    mode_re, mode_im, mul_neg, Real.cos_neg, Real.sin_neg]
  norm_num
  ring

theorem real_cosine_hasSum (φ : ℝ) :
    HasSum (fun n : ℤ => (angularCoefficient 0 n).re*Real.cos ((n : ℝ)*φ)) (angular φ) := by
  have h := Complex.hasSum_re (((angular_hasSum φ).add (angular_hasSum (-φ))).div_const 2)
  simpa only [mode_pair_real, angular_even, add_self_div_two, Complex.ofReal_re] using h

theorem cosineCoefficient_hasSum (φ : ℝ) :
    HasSum (fun j : ℕ => cosineCoefficient j*Real.cos ((j : ℝ)*φ)) (angular φ) := by
  have h := ((real_cosine_hasSum φ).nat_add_neg).sub
    (hasSum_ite_eq (0 : ℕ) ((angularCoefficient 0 0).re))
  simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one, add_sub_cancel_right] at h
  convert h using 1
  funext j
  by_cases hj : j = 0
  · subst j
    simp only [cosineCoefficient, ↓reduceIte, Nat.cast_zero, Int.cast_zero, neg_zero,
      zero_mul, Real.cos_zero, mul_one]
    ring
  · simp only [cosineCoefficient, hj, ↓reduceIte, Int.cast_natCast, Int.cast_neg, neg_mul, Real.cos_neg, sub_zero]
    ring

theorem cosineCoefficient_decay (j : ℕ) :
    |cosineCoefficient j| ≤ 48*Real.exp (-Real.sqrt j/64) := by
  have hp := angularCoefficient_decay (j : ℤ)
  have hm := angularCoefficient_decay (-(j : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j)] at hp hm
  by_cases hj : j = 0
  · subst j
    simp only [cosineCoefficient, ↓reduceIte]
    have h := (Complex.abs_re_le_norm (angularCoefficient 0 0)).trans hp
    norm_num at h ⊢
    linarith
  · rw [cosineCoefficient, ite_eq_right hj]
    calc
      _ ≤ |(angularCoefficient 0 (j : ℤ)).re|+|(angularCoefficient 0 (-(j : ℤ))).re| := abs_add_le _ _
      _ ≤ ‖angularCoefficient 0 (j : ℤ)‖+‖angularCoefficient 0 (-(j : ℤ))‖ :=
        add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
      _ ≤ _ := by linarith

theorem cosineCoefficient_weighted_summable :
    Summable (fun j : ℕ => (1+(j : ℝ)^2)*|cosineCoefficient j|) := by
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ (weighted_exp_summable.mul_left 48)
  intro j
  have he : Real.exp (-Real.sqrt (j : ℝ)/64) ≤ Real.exp (-Real.sqrt j/128) :=
    Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (j : ℝ)])
  calc
    _ ≤ (1+(j : ℝ)^2)*(48*Real.exp (-Real.sqrt j/64)) :=
      mul_le_mul_of_nonneg_left (cosineCoefficient_decay j) (by positivity)
    _ ≤ (1+(j : ℝ)^2)*(48*Real.exp (-Real.sqrt j/128)) := by gcongr
    _ = _ := by ring

theorem cosineCoefficient_weighted_tail (D : ℕ) :
    (∑' j : ℕ, if D ≤ j then (1+(j : ℝ)^2)*|cosineCoefficient j| else 0) ≤
      (2 : ℝ)^87*Real.exp (-Real.sqrt D/128) := by
  have hmajor (j : ℕ) :
      (if D ≤ j then (1+(j : ℝ)^2)*|cosineCoefficient j| else 0) ≤
      48*(if D ≤ j then (1+(j : ℝ)^2)*Real.exp (-Real.sqrt j/64) else 0) := by
    split_ifs with hj
    · have h := mul_le_mul_of_nonneg_left (cosineCoefficient_decay j)
        (show 0 ≤ 1+(j : ℝ)^2 by positivity)
      nlinarith only [h]
    · simp
  have hsum : Summable (fun j : ℕ => if D ≤ j then
      (1+(j : ℝ)^2)*Real.exp (-Real.sqrt j/64) else 0) := by
    apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) _ weighted_exp_summable
    intro j
    split_ifs
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (j : ℝ)])
    · positivity
  have ht : Summable (fun j : ℕ => if D ≤ j then (1+(j : ℝ)^2)*|cosineCoefficient j| else 0) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) hmajor (hsum.mul_left 48)
  calc
    _ ≤ ∑' j : ℕ, 48*(if D ≤ j then (1+(j : ℝ)^2)*Real.exp (-Real.sqrt j/64) else 0) :=
      Summable.tsum_le_tsum hmajor ht (hsum.mul_left 48)
    _ = 48*(∑' j : ℕ, if D ≤ j then (1+(j : ℝ)^2)*Real.exp (-Real.sqrt j/64) else 0) := tsum_mul_left
    _ ≤ 48*((2 : ℝ)^81*Real.exp (-Real.sqrt D/128)) :=
      mul_le_mul_of_nonneg_left (weighted_exp_tail D) (by norm_num)
    _ ≤ _ := by nlinarith only [Real.exp_pos (-Real.sqrt (D : ℝ)/128)]

#print axioms cosineCoefficient_hasSum
#print axioms cosineCoefficient_weighted_tail

end Maxwell.Continuum.Profile
