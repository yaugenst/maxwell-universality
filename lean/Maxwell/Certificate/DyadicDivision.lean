import Maxwell.Certificate.DyadicRectangle

/-! Integer corner checks for division by a positive real interval. -/
namespace Maxwell.Certificate.DyadicRectangle

private theorem linear_upper_of_endpoints (a l u x b : ℝ)
    (hl : l ≤ x) (hu : x ≤ u) (h₁ : a*l ≤ b) (h₂ : a*u ≤ b) : a*x ≤ b := by
  by_cases ha : 0 ≤ a
  · exact (mul_le_mul_of_nonneg_left hu ha).trans h₂
  · exact (mul_le_mul_of_nonpos_left hl (le_of_not_ge ha)).trans h₁

private theorem linear_lower_of_endpoints (a l u x b : ℝ)
    (hl : l ≤ x) (hu : x ≤ u) (h₁ : b ≤ a*l) (h₂ : b ≤ a*u) : b ≤ a*x := by
  by_cases ha : 0 ≤ a
  · exact h₁.trans (mul_le_mul_of_nonneg_left hl ha)
  · exact h₂.trans (mul_le_mul_of_nonpos_left hu (le_of_not_ge ha))

private theorem real_div_bounds (α β s nl nu dl du cl cu : ℝ)
    (hs : 0 < s) (hd : 0 < dl) (hα : nl ≤ α ∧ α ≤ nu) (hβ : dl ≤ β ∧ β ≤ du)
    (h₁ : cl*dl ≤ nl*s) (h₂ : cl*du ≤ nl*s)
    (h₃ : nu*s ≤ cu*dl) (h₄ : nu*s ≤ cu*du) :
    cl ≤ α*s/β ∧ α*s/β ≤ cu := by
  have hβpos : 0 < β := hd.trans_le hβ.1
  constructor
  · apply (le_div_iff₀ hβpos).mpr
    exact (linear_upper_of_endpoints cl dl du β (nl*s) hβ.1 hβ.2 h₁ h₂).trans
      (mul_le_mul_of_nonneg_right hα.1 hs.le)
  · apply (div_le_iff₀ hβpos).mpr
    exact (mul_le_mul_of_nonneg_right hα.2 hs.le).trans
      (linear_lower_of_endpoints cu dl du β (nu*s) hβ.1 hβ.2 h₃ h₄)

def channelDivCheck (p : ℕ) (a : ℤ) (ar : ℕ) (b : ℤ) (br : ℕ)
    (c : ℤ) (cr : ℕ) : Bool :=
  let s : ℤ := 2^p
  decide ((c-cr)*(b-br) ≤ (a-ar)*s ∧ (c-cr)*(b+br) ≤ (a-ar)*s ∧
    (a+ar)*s ≤ (c+cr)*(b-br) ∧ (a+ar)*s ≤ (c+cr)*(b+br))

def divCheck (p : ℕ) (a b c : DyadicRectangle) : Bool :=
  decide (0 < b.re-(b.radius:ℤ)) &&
    channelDivCheck p a.re a.radius b.re b.radius c.re c.radius &&
    channelDivCheck p a.im a.radius b.re b.radius c.im c.radius

private theorem channelDivCheck_sound {p : ℕ} {a b c : ℤ} {ar br cr : ℕ} {x y : ℝ}
    (hp : 0 < b-(br:ℤ)) (h : channelDivCheck p a ar b br c cr = true)
    (hx : |x*2^p-a| ≤ ar) (hy : |y*2^p-b| ≤ br) :
    |(x/y)*2^p-c| ≤ cr := by
  have hs : (0:ℝ) < 2^p := by positivity
  have hb : (0:ℝ) < b-(br:ℝ) := by exact_mod_cast hp
  have hh : (c-cr)*(b-br) ≤ (a-ar)*(2:ℤ)^p ∧
      (c-cr)*(b+br) ≤ (a-ar)*(2:ℤ)^p ∧
      (a+ar)*(2:ℤ)^p ≤ (c+cr)*(b-br) ∧
      (a+ar)*(2:ℤ)^p ≤ (c+cr)*(b+br) := of_decide_eq_true h
  have h₁ : ((c:ℝ)-cr)*(b-br) ≤ (a-ar)*(2:ℝ)^p := by exact_mod_cast hh.1
  have h₂ : ((c:ℝ)-cr)*(b+br) ≤ (a-ar)*(2:ℝ)^p := by exact_mod_cast hh.2.1
  have h₃ : ((a:ℝ)+ar)*(2:ℝ)^p ≤ (c+cr)*(b-br) := by exact_mod_cast hh.2.2.1
  have h₄ : ((a:ℝ)+ar)*(2:ℝ)^p ≤ (c+cr)*(b+br) := by exact_mod_cast hh.2.2.2
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hbound := real_div_bounds (x*2^p) (y*2^p) (2^p)
    (a-ar) (a+ar) (b-br) (b+br) (c-cr) (c+cr) hs hb
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h₁ h₂ h₃ h₄
  have hypos : 0 < y := by nlinarith
  have he : x*2^p*2^p/(y*2^p) = (x/y)*2^p := by field_simp
  rw [he] at hbound
  exact abs_le.mpr ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

theorem divCheck_sound {p : ℕ} {a b c : DyadicRectangle} {z : ℂ} {x : ℝ}
    (h : divCheck p a b c = true) (ha : a.Contains p z)
    (hb : b.Contains p (x:ℂ)) : c.Contains p (z/(x:ℂ)) := by
  simp only [divCheck, Bool.and_eq_true_iff] at h
  have hp : 0 < b.re-(b.radius:ℤ) := of_decide_eq_true h.1.1
  constructor
  · simpa only [Complex.div_ofReal_re, Complex.ofReal_re] using channelDivCheck_sound hp h.1.2 ha.1 hb.1
  · simpa only [Complex.div_ofReal_im, Complex.ofReal_re] using channelDivCheck_sound hp h.2 ha.2 hb.1

end Maxwell.Certificate.DyadicRectangle
