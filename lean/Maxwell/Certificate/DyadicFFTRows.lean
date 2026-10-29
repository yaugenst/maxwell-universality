import Maxwell.Certificate.DyadicFFT

/-! Opaque assembly lemmas prevent a closed large FFT predicate from being
reduced again when its individual rows have already been kernel checked. -/
namespace Maxwell.Certificate.DyadicFFT

open Maxwell.Spectral.PrimitiveYee

theorem axisXCheck_of_rows (p q : ℕ) (K : Kernel 20) (input output : Field)
    (h : ∀ r, DyadicRectangle.dotCheck p q (fun x => input (x, r.2))
      (fun x => K r.1 x) (output r) = true) :
    axisXCheck p q K input output = true := decide_eq_true h

theorem axisYCheck_of_rows (p q : ℕ) (K : Kernel 10) (input output : Field)
    (h : ∀ r, DyadicRectangle.dotCheck p q (fun y => input (r.1, y, r.2.2))
      (fun y => K r.2.1 y) (output r) = true) :
    axisYCheck p q K input output = true := decide_eq_true h

theorem axisZCheck_of_rows (p q : ℕ) (K : Kernel 10) (input output : Field)
    (h : ∀ r, DyadicRectangle.dotCheck p q (fun z => input (r.1, r.2.1, z))
      (fun z => K r.2.2 z) (output r) = true) :
    axisZCheck p q K input output = true := decide_eq_true h

theorem diagonalCheck_of_rows (p q : ℕ) (t input output : Field)
    (h : ∀ r, DyadicRectangle.rescaleCheck p q
      (DyadicRectangle.mulExact (input r) (t r)) (output r) = true) :
    diagonalCheck p q t input output = true := decide_eq_true h

theorem inverseCheck_of_stages (p q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal)
    (hZ : axisZCheck p q (adjoint K10) input w.first = true)
    (hY : axisYCheck p q (adjoint K10) w.first w.second = true)
    (hT : diagonalCheck p q (conjugate twiddle) w.second w.third = true)
    (hX : axisXCheck p q (adjoint K20) w.third w.result = true) :
    inverseCheck p q K20 K10 twiddle input w = true := by
  simp only [inverseCheck, hZ, hY, hT, hX, Bool.and_self]

theorem forwardCheck_of_stages (p q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal)
    (hX : axisXCheck p q K20 input w.first = true)
    (hT : diagonalCheck p q twiddle w.first w.second = true)
    (hY : axisYCheck p q K10 w.second w.third = true)
    (hZ : axisZCheck p q K10 w.third w.result = true) :
    forwardCheck p q K20 K10 twiddle input w = true := by
  simp only [forwardCheck, hX, hT, hY, hZ, Bool.and_self]

end Maxwell.Certificate.DyadicFFT
