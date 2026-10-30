import Maxwell.Continuum.AlmostAnalyticCutoffSize
import Mathlib.Data.Nat.Choose.Bounds

/-! Symbolic factorial bounds for mixed spatial derivatives of the
truncated Gevrey extension. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

theorem factorial_add_le_geometric (m j : ℕ) :
    ((m+j).factorial : ℝ) ≤ (2 : ℝ)^(m+j)*(m.factorial : ℝ)*(j.factorial : ℝ) := by
  have he : ((m+j).factorial : ℝ) = ((m+j).choose j : ℝ)*m.factorial*j.factorial := by
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial m j).symm
  rw [he]
  gcongr
  exact_mod_cast Nat.choose_le_two_pow (m+j) j

theorem mixed_factorial_majorant {b : ℝ} (hb : 0 < b) (m j : ℕ)
    (hj : j ≤ truncationOrder ((2 : ℝ)^156*b)) :
    (1/(j.factorial : ℝ))*b^j*((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*((m+j).factorial : ℝ)^2) ≤
      ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*(1/2 : ℝ)^j := by
  have hf := factorial_add_le_geometric m j
  have hjf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have he : (1/(j.factorial : ℝ))*b^j*((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*
      ((2 : ℝ)^(m+j)*(m.factorial : ℝ)*(j.factorial : ℝ))^2) =
      ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*
        (((2 : ℝ)^154*b)^j*(j.factorial : ℝ)) := by
    rw [pow_add, pow_add]
    simp only [mul_pow, ← pow_mul]
    field_simp
    ring_nf
  calc
    _ ≤ (1/(j.factorial : ℝ))*b^j*((2 : ℝ)^12*((2 : ℝ)^152)^(m+j)*
        ((2 : ℝ)^(m+j)*(m.factorial : ℝ)*(j.factorial : ℝ))^2) := by gcongr
    _ = _ := he
    _ ≤ ((2 : ℝ)^12*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2)*
        (((2 : ℝ)^156*b)^j*(j.factorial : ℝ)) := by
      gcongr <;> norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (truncated_factorial_term (mul_pos (by positivity) hb) hj) (by positivity)

#print axioms mixed_factorial_majorant

end Maxwell.Continuum.AlmostAnalytic
