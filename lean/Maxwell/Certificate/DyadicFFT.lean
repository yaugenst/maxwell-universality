import Maxwell.Certificate.DyadicRectangle
import Maxwell.Certificate.FourierStages

/-! Integer-only stage checks for the actual primitive FCC Fourier transform.
Input and output rectangles use precision `p`; coefficients use precision `q`.
Each axis output is checked with one exact integer dot product. -/
namespace Maxwell.Certificate.DyadicFFT

open Matrix Maxwell.Spectral.PrimitiveYee FourierBinding

abbrev Field := Cell → DyadicRectangle
abbrev Kernel (n : ℕ) := Matrix (Fin n) (Fin n) DyadicRectangle

def Contains (p : ℕ) (a : Field) (v : Cell → ℂ) : Prop :=
  ∀ r, (a r).Contains p (v r)

def KernelContains {n : ℕ} (q : ℕ) (a : Kernel n)
    (v : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, (a i j).Contains q (v i j)

def axisXCheck (p q : ℕ) (K : Kernel 20) (input output : Field) : Bool :=
  decide (∀ r, DyadicRectangle.dotCheck p q (fun x => input (x, r.2))
    (fun x => K r.1 x) (output r) = true)

def axisYCheck (p q : ℕ) (K : Kernel 10) (input output : Field) : Bool :=
  decide (∀ r, DyadicRectangle.dotCheck p q (fun y => input (r.1, y, r.2.2))
    (fun y => K r.2.1 y) (output r) = true)

def axisZCheck (p q : ℕ) (K : Kernel 10) (input output : Field) : Bool :=
  decide (∀ r, DyadicRectangle.dotCheck p q (fun z => input (r.1, r.2.1, z))
    (fun z => K r.2.2 z) (output r) = true)

def diagonalCheck (p q : ℕ) (t input output : Field) : Bool :=
  decide (∀ r, DyadicRectangle.rescaleCheck p q
    (DyadicRectangle.mulExact (input r) (t r)) (output r) = true)

theorem axisXCheck_sound {p q : ℕ} {K : Kernel 20} {input output : Field}
    {M : Matrix (Fin 20) (Fin 20) ℂ} {v : Cell → ℂ}
    (hK : KernelContains q K M) (hv : Contains p input v)
    (h : axisXCheck p q K input output = true) :
    Contains p output (FourierBinding.axisX M *ᵥ v) := by
  have hh := of_decide_eq_true h
  intro r
  rw [axisX_mulVec]
  simpa only [mul_comm] using DyadicRectangle.dotCheck_sound (hh r)
    (fun x => hv (x, r.2)) (hK r.1)

theorem axisYCheck_sound {p q : ℕ} {K : Kernel 10} {input output : Field}
    {M : Matrix (Fin 10) (Fin 10) ℂ} {v : Cell → ℂ}
    (hK : KernelContains q K M) (hv : Contains p input v)
    (h : axisYCheck p q K input output = true) :
    Contains p output (FourierBinding.axisY M *ᵥ v) := by
  have hh := of_decide_eq_true h
  intro r
  rw [axisY_mulVec]
  simpa only [mul_comm] using DyadicRectangle.dotCheck_sound (hh r)
    (fun y => hv (r.1, y, r.2.2)) (hK r.2.1)

theorem axisZCheck_sound {p q : ℕ} {K : Kernel 10} {input output : Field}
    {M : Matrix (Fin 10) (Fin 10) ℂ} {v : Cell → ℂ}
    (hK : KernelContains q K M) (hv : Contains p input v)
    (h : axisZCheck p q K input output = true) :
    Contains p output (FourierBinding.axisZ M *ᵥ v) := by
  have hh := of_decide_eq_true h
  intro r
  rw [axisZ_mulVec]
  simpa only [mul_comm] using DyadicRectangle.dotCheck_sound (hh r)
    (fun z => hv (r.1, r.2.1, z)) (hK r.2.2)

theorem diagonalCheck_sound {p q : ℕ} {t input output : Field}
    {a v : Cell → ℂ} (ht : Contains q t a) (hv : Contains p input v)
    (h : diagonalCheck p q t input output = true) :
    Contains p output (Matrix.diagonal a *ᵥ v) := by
  have hh := of_decide_eq_true h
  intro r
  simpa only [Matrix.mulVec_diagonal, mul_comm] using
    DyadicRectangle.rescaleCheck_sound (hh r)
      (DyadicRectangle.mulExact_contains (hv r) (ht r))

def adjoint {n : ℕ} (K : Kernel n) : Kernel n := fun i j => (K j i).conjugate

theorem adjoint_contains {n q : ℕ} {K : Kernel n} {M : Matrix (Fin n) (Fin n) ℂ}
    (hK : KernelContains q K M) : KernelContains q (adjoint K) M.conjTranspose :=
  fun i j => DyadicRectangle.conjugate_contains (hK j i)

def conjugate (t : Field) : Field := fun r => (t r).conjugate

theorem conjugate_contains {q : ℕ} {t : Field} {a : Cell → ℂ}
    (ht : Contains q t a) : Contains q (conjugate t) (star a) :=
  fun r => DyadicRectangle.conjugate_contains (ht r)

structure Proposal where
  first : Field
  second : Field
  third : Field
  result : Field

def inverseCheck (p q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal) : Bool :=
  axisZCheck p q (adjoint K10) input w.first &&
  axisYCheck p q (adjoint K10) w.first w.second &&
  diagonalCheck p q (conjugate twiddle) w.second w.third &&
  axisXCheck p q (adjoint K20) w.third w.result

theorem inverseCheck_sound {p q : ℕ} (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal)
    (h20 : KernelContains q K20 (cyclicFourier 20))
    (h10 : KernelContains q K10 (cyclicFourier 10))
    (ht : Contains q twiddle fccTwiddle) (v : Cell → ℂ) (hv : Contains p input v)
    (h : inverseCheck p q K20 K10 twiddle input w = true) :
    Contains p w.result (transform 0 *ᵥ v) := by
  simp only [inverseCheck, Bool.and_eq_true_iff] at h
  have h1 := axisZCheck_sound (adjoint_contains h10) hv h.1.1.1
  have h2 := axisYCheck_sound (adjoint_contains h10) h1 h.1.1.2
  have h3 := diagonalCheck_sound (conjugate_contains ht) h2 h.1.2
  have h4 := axisXCheck_sound (adjoint_contains h20) h3 h.2
  rw [← inverseFFT_eq_transform, inverseFFT, axisX_conjTranspose, axisY_conjTranspose,
    axisZ_conjTranspose, Matrix.diagonal_conjTranspose]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

def forwardCheck (p q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal) : Bool :=
  axisXCheck p q K20 input w.first &&
  diagonalCheck p q twiddle w.first w.second &&
  axisYCheck p q K10 w.second w.third &&
  axisZCheck p q K10 w.third w.result

theorem forwardCheck_sound {p q : ℕ} (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) (w : Proposal)
    (h20 : KernelContains q K20 (cyclicFourier 20))
    (h10 : KernelContains q K10 (cyclicFourier 10))
    (ht : Contains q twiddle fccTwiddle) (v : Cell → ℂ) (hv : Contains p input v)
    (h : forwardCheck p q K20 K10 twiddle input w = true) :
    Contains p w.result ((transform 0).conjTranspose *ᵥ v) := by
  simp only [forwardCheck, Bool.and_eq_true_iff] at h
  have h1 := axisXCheck_sound h20 hv h.1.1.1
  have h2 := diagonalCheck_sound ht h1 h.1.1.2
  have h3 := axisYCheck_sound h10 h2 h.1.2
  have h4 := axisZCheck_sound h10 h3 h.2
  rw [← forwardFFT_eq_conjTranspose, forwardFFT]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

end Maxwell.Certificate.DyadicFFT
