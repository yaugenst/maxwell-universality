import Maxwell.Certificate.FourierRoots
import Maxwell.Certificate.IntervalLinear

/-! Sound interval certificates for the sparse FCC FFT stages. Each axis
output uses 10 or 20 products. Proposed outputs can be rounded between stages;
the final semantics is the actual unitary FCC Fourier transform. -/

namespace Maxwell.Certificate.FFTInterval

open Matrix Maxwell.Spectral.PrimitiveYee FourierBinding

abbrev Field := Cell → ComplexRectangle

def Contains (a : Field) (v : Cell → ℂ) : Prop := ∀ p, (a p).Contains (v p)

def subsetCheck (a b : Field) : Bool :=
  decide (∀ p, Trigonometric.rectangleSubsetCheck (a p) (b p) = true)

theorem subsetCheck_sound {a b : Field} {v : Cell → ℂ}
    (h : subsetCheck a b = true) (hv : Contains a v) : Contains b v := by
  have hh : ∀ p, Trigonometric.rectangleSubsetCheck (a p) (b p) = true :=
    of_decide_eq_true h
  exact fun p => Trigonometric.rectangleSubsetCheck_sound (hh p) (hv p)

def axisX (K : IntervalLinear.Rectangular 20 20) (v : Field) : Field :=
  fun p => IntervalLinear.sum fun x => (K p.1 x).mul (v (x, p.2))

def axisY (K : IntervalLinear.Rectangular 10 10) (v : Field) : Field :=
  fun p => IntervalLinear.sum fun y => (K p.2.1 y).mul (v (p.1, y, p.2.2))

def axisZ (K : IntervalLinear.Rectangular 10 10) (v : Field) : Field :=
  fun p => IntervalLinear.sum fun z => (K p.2.2 z).mul (v (p.1, p.2.1, z))

def diagonal (t v : Field) : Field := fun p => (t p).mul (v p)

theorem axisX_contains {K : IntervalLinear.Rectangular 20 20} {v : Field}
    {M : Matrix (Fin 20) (Fin 20) ℂ} {w : Cell → ℂ}
    (hK : IntervalLinear.Contains K M) (hv : Contains v w) :
    Contains (axisX K v) (FourierBinding.axisX M *ᵥ w) := by
  intro p
  rw [axisX_mulVec]
  exact IntervalLinear.sum_contains fun x => ComplexRectangle.contains_mul (hK p.1 x) (hv (x, p.2))

theorem axisY_contains {K : IntervalLinear.Rectangular 10 10} {v : Field}
    {M : Matrix (Fin 10) (Fin 10) ℂ} {w : Cell → ℂ}
    (hK : IntervalLinear.Contains K M) (hv : Contains v w) :
    Contains (axisY K v) (FourierBinding.axisY M *ᵥ w) := by
  intro p
  rw [axisY_mulVec]
  exact IntervalLinear.sum_contains fun y =>
    ComplexRectangle.contains_mul (hK p.2.1 y) (hv (p.1, y, p.2.2))

theorem axisZ_contains {K : IntervalLinear.Rectangular 10 10} {v : Field}
    {M : Matrix (Fin 10) (Fin 10) ℂ} {w : Cell → ℂ}
    (hK : IntervalLinear.Contains K M) (hv : Contains v w) :
    Contains (axisZ K v) (FourierBinding.axisZ M *ᵥ w) := by
  intro p
  rw [axisZ_mulVec]
  exact IntervalLinear.sum_contains fun z =>
    ComplexRectangle.contains_mul (hK p.2.2 z) (hv (p.1, p.2.1, z))

theorem diagonal_contains {t v : Field} {a w : Cell → ℂ}
    (ht : Contains t a) (hv : Contains v w) :
    Contains (diagonal t v) (Matrix.diagonal a *ᵥ w) := by
  intro p
  simpa only [diagonal, Matrix.mulVec_diagonal] using
    ComplexRectangle.contains_mul (ht p) (hv p)

def adjoint {n : ℕ} (K : IntervalLinear.Rectangular n n) : IntervalLinear.Rectangular n n :=
  fun i j => (K j i).conjugate

theorem adjoint_contains {n : ℕ} {K : IntervalLinear.Rectangular n n}
    {M : Matrix (Fin n) (Fin n) ℂ} (hK : IntervalLinear.Contains K M) :
    IntervalLinear.Contains (adjoint K) M.conjTranspose :=
  fun i j => ComplexRectangle.contains_conjugate (hK j i)

def conjugate (t : Field) : Field := fun p => (t p).conjugate

theorem conjugate_contains {t : Field} {a : Cell → ℂ} (ht : Contains t a) :
    Contains (conjugate t) (star a) := fun p => ComplexRectangle.contains_conjugate (ht p)

structure Proposal where
  first : Field
  second : Field
  third : Field
  result : Field

def forwardCheck (K20 : IntervalLinear.Rectangular 20 20)
    (K10 : IntervalLinear.Rectangular 10 10) (twiddle input : Field) (w : Proposal) : Bool :=
  subsetCheck (axisX K20 input) w.first &&
    subsetCheck (diagonal twiddle w.first) w.second &&
    subsetCheck (axisY K10 w.second) w.third &&
    subsetCheck (axisZ K10 w.third) w.result

theorem forwardCheck_sound (K20 : IntervalLinear.Rectangular 20 20)
    (K10 : IntervalLinear.Rectangular 10 10) (twiddle input : Field) (w : Proposal)
    (h20 : IntervalLinear.Contains K20 (cyclicFourier 20))
    (h10 : IntervalLinear.Contains K10 (cyclicFourier 10))
    (ht : Contains twiddle fccTwiddle) (v : Cell → ℂ) (hv : Contains input v)
    (h : forwardCheck K20 K10 twiddle input w = true) :
    Contains w.result ((transform 0).conjTranspose *ᵥ v) := by
  simp only [forwardCheck, Bool.and_eq_true_iff] at h
  have h1 := subsetCheck_sound h.1.1.1 (axisX_contains h20 hv)
  have h2 := subsetCheck_sound h.1.1.2 (diagonal_contains ht h1)
  have h3 := subsetCheck_sound h.1.2 (axisY_contains h10 h2)
  have h4 := subsetCheck_sound h.2 (axisZ_contains h10 h3)
  rw [← forwardFFT_eq_conjTranspose, forwardFFT]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

def inverseCheck (K20 : IntervalLinear.Rectangular 20 20)
    (K10 : IntervalLinear.Rectangular 10 10) (twiddle input : Field) (w : Proposal) : Bool :=
  subsetCheck (axisZ (adjoint K10) input) w.first &&
    subsetCheck (axisY (adjoint K10) w.first) w.second &&
    subsetCheck (diagonal (conjugate twiddle) w.second) w.third &&
    subsetCheck (axisX (adjoint K20) w.third) w.result

theorem inverseCheck_sound (K20 : IntervalLinear.Rectangular 20 20)
    (K10 : IntervalLinear.Rectangular 10 10) (twiddle input : Field) (w : Proposal)
    (h20 : IntervalLinear.Contains K20 (cyclicFourier 20))
    (h10 : IntervalLinear.Contains K10 (cyclicFourier 10))
    (ht : Contains twiddle fccTwiddle) (v : Cell → ℂ) (hv : Contains input v)
    (h : inverseCheck K20 K10 twiddle input w = true) :
    Contains w.result (transform 0 *ᵥ v) := by
  simp only [inverseCheck, Bool.and_eq_true_iff] at h
  have h1 := subsetCheck_sound h.1.1.1 (axisZ_contains (adjoint_contains h10) hv)
  have h2 := subsetCheck_sound h.1.1.2 (axisY_contains (adjoint_contains h10) h1)
  have h3 := subsetCheck_sound h.1.2 (diagonal_contains (conjugate_contains ht) h2)
  have h4 := subsetCheck_sound h.2 (axisX_contains (adjoint_contains h20) h3)
  rw [← inverseFFT_eq_transform, inverseFFT, axisX_conjTranspose, axisY_conjTranspose,
    axisZ_conjTranspose, Matrix.diagonal_conjTranspose]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

end Maxwell.Certificate.FFTInterval
