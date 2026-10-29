import Maxwell.Certificate.DyadicRectangle

namespace Maxwell.Certificate.DyadicRectangle

def scaleCheck (num den : ℤ) : DyadicRectangle → DyadicRectangle → Bool
  | ⟨ar, ai, ae⟩, ⟨cr, ci, ce⟩ =>
    decide (0 < den ∧ |ar*num-cr*den|+(ae:ℤ)*|num| ≤ ce*den ∧
      |ai*num-ci*den|+(ae:ℤ)*|num| ≤ ce*den)

private theorem channel_scale (x a r n d c s : ℝ) (hd : 0 < d)
    (hx : |x-a| ≤ r) (h : |a*n-c*d|+r*|n| ≤ s*d) : |x*n/d-c| ≤ s := by
  have he : x*n/d-c = ((x-a)*n+(a*n-c*d))/d := by field_simp; ring
  rw [he, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ |(x-a)*n|+|a*n-c*d| := abs_add_le _ _
    _ ≤ r*|n|+|a*n-c*d| := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hx (abs_nonneg n)) le_rfl
    _ ≤ _ := by linarith

theorem scaleCheck_sound {p : ℕ} {num den : ℤ} {a c : DyadicRectangle} {z : ℂ}
    (h : scaleCheck num den a c = true) (ha : a.Contains p z) :
    c.Contains p (z*(num:ℂ)/(den:ℂ)) := by
  rcases a with ⟨ar, ai, ae⟩
  rcases c with ⟨cr, ci, ce⟩
  have hh : 0 < den ∧ |ar*num-cr*den|+(ae:ℤ)*|num| ≤ ce*den ∧
      |ai*num-ci*den|+(ae:ℤ)*|num| ≤ ce*den := of_decide_eq_true h
  have hd : (0:ℝ)<den := by exact_mod_cast hh.1
  have hre : |(ar:ℝ)*num-cr*den|+ae*|(num:ℝ)| ≤ ce*den := by exact_mod_cast hh.2.1
  have him : |(ai:ℝ)*num-ci*den|+ae*|(num:ℝ)| ≤ ce*den := by exact_mod_cast hh.2.2
  have hr := channel_scale (z.re*2^p) ar ae num den cr ce hd ha.1 hre
  have hi := channel_scale (z.im*2^p) ai ae num den ci ce hd ha.2 him
  have hn : (num:ℂ) = ((num:ℝ):ℂ) := by simp
  have hdn : (den:ℂ) = ((den:ℝ):ℂ) := by simp
  rw [hn, hdn]
  constructor
  · simp only [Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    convert hr using 1
    congr 1
    ring
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    convert hi using 1
    congr 1
    ring

end Maxwell.Certificate.DyadicRectangle
