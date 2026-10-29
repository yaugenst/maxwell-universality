import Maxwell.Certificate.FourierStages

/-! The sparse FFT stages use the same twenty roots of unity as the frozen
interval kernel. These identities connect its root/normalization rectangles
to the exact stage matrices. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee

def root20 (m : ℤ) : ℂ := Trigonometric.cis (((m % 20 : ℤ) : ℚ) / 20)

theorem root20_eq_cis (m : ℤ) : root20 m = Trigonometric.cis ((m : ℚ) / 20) := by
  have hZ := congrArg ((↑) : ℤ → ℚ) (Int.emod_add_mul_ediv m 20)
  push_cast at hZ
  have hq : (m : ℚ) / 20 = ((m % 20 : ℤ) : ℚ) / 20 + ((m / 20 : ℤ) : ℚ) := by
    linarith
  rw [hq, cis_add_int]
  rfl

theorem cis_conjugate (q : ℚ) : star (Trigonometric.cis q) = Trigonometric.cis (-q) := by
  unfold Trigonometric.cis
  change starRingEnd ℂ (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  norm_num
  left
  change star (2 : ℂ) = 2
  exact star_ofNat 2

theorem cyclicFourier_eq_cis (n : ℕ) (a b : Fin n) :
    cyclicFourier n a b = (((Real.sqrt n : ℝ) : ℂ))⁻¹ *
      star (Trigonometric.cis (((a.val : ℚ) * b.val) / n)) := by
  rw [cis_conjugate]
  unfold cyclicFourier Trigonometric.cis
  congr 2
  push_cast
  ring

theorem cyclicFourier_twenty_root (a b : Fin 20) :
    cyclicFourier 20 a b = (((Real.sqrt 20 : ℝ) : ℂ))⁻¹ *
      star (root20 ((a.val : ℤ) * b.val)) := by
  rw [cyclicFourier_eq_cis, root20_eq_cis]
  push_cast
  rfl

theorem cyclicFourier_ten_root (a b : Fin 10) :
    cyclicFourier 10 a b = (((Real.sqrt 10 : ℝ) : ℂ))⁻¹ *
      star (root20 (2 * (a.val : ℤ) * b.val)) := by
  rw [cyclicFourier_eq_cis, root20_eq_cis]
  congr 3
  push_cast
  ring

theorem fccTwiddle_eq_root (p : Cell) :
    fccTwiddle p = root20 ((p.1.val : ℤ) * (p.2.1.val + p.2.2.val)) := by
  rw [root20_eq_cis]
  unfold fccTwiddle Trigonometric.cis
  congr 1
  push_cast
  ring

theorem root20_rectangle_contains (m : ℤ) (proposed : ComplexRectangle)
    (h : Trigonometric.cisCheck (((m % 20 : ℤ) : ℚ) / 20) proposed = true) :
    proposed.Contains (root20 m) := Trigonometric.cisCheck_sound h

theorem cyclicFourier_twenty_contains (a b : Fin 20) (root : ComplexRectangle) (norm : Ball)
    (hr : Trigonometric.cisCheck (((((a.val : ℤ) * b.val) % 20 : ℤ) : ℚ) / 20) root = true)
    (hn : norm.Contains (1 / Real.sqrt 20)) :
    ((IntervalMatrix.realRectangle norm).mul root.conjugate).Contains (cyclicFourier 20 a b) := by
  rw [cyclicFourier_twenty_root]
  have h := ComplexRectangle.contains_mul (IntervalMatrix.realRectangle_contains hn)
    (ComplexRectangle.contains_conjugate (root20_rectangle_contains _ root hr))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, one_mul] using h

theorem cyclicFourier_ten_contains (a b : Fin 10) (root : ComplexRectangle) (norm : Ball)
    (hr : Trigonometric.cisCheck ((((2 * (a.val : ℤ) * b.val) % 20 : ℤ) : ℚ) / 20) root = true)
    (hn : norm.Contains (1 / Real.sqrt 10)) :
    ((IntervalMatrix.realRectangle norm).mul root.conjugate).Contains (cyclicFourier 10 a b) := by
  rw [cyclicFourier_ten_root]
  have h := ComplexRectangle.contains_mul (IntervalMatrix.realRectangle_contains hn)
    (ComplexRectangle.contains_conjugate (root20_rectangle_contains _ root hr))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, one_mul] using h

end Maxwell.Certificate.FourierBinding
