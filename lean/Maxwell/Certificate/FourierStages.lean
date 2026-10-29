import Maxwell.Certificate.FourierEnclosure

/-! Sparse axis stages of the fixed FCC Fourier transform. Each axis stage
has only 10 or 20 terms per output, as in the certificate producer. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee

def axisX (K : Matrix (Fin 20) (Fin 20) ℂ) : Matrix Cell Cell ℂ :=
  fun p q => if p.2 = q.2 then K p.1 q.1 else 0

def axisY (K : Matrix (Fin 10) (Fin 10) ℂ) : Matrix Cell Cell ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.2 = q.2.2 then K p.2.1 q.2.1 else 0

def axisZ (K : Matrix (Fin 10) (Fin 10) ℂ) : Matrix Cell Cell ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then K p.2.2 q.2.2 else 0

theorem axisX_mulVec (K : Matrix (Fin 20) (Fin 20) ℂ) (v : Cell → ℂ) (p : Cell) :
    (axisX K *ᵥ v) p = ∑ x : Fin 20, K p.1 x * v (x, p.2) := by
  simp [axisX, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem axisY_mulVec (K : Matrix (Fin 10) (Fin 10) ℂ) (v : Cell → ℂ) (p : Cell) :
    (axisY K *ᵥ v) p = ∑ y : Fin 10, K p.2.1 y * v (p.1, y, p.2.2) := by
  simp [axisY, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, ite_and]

theorem axisZ_mulVec (K : Matrix (Fin 10) (Fin 10) ℂ) (v : Cell → ℂ) (p : Cell) :
    (axisZ K *ᵥ v) p = ∑ z : Fin 10, K p.2.2 z * v (p.1, p.2.1, z) := by
  simp [axisZ, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, ite_and]

theorem axisX_conjTranspose (K : Matrix (Fin 20) (Fin 20) ℂ) :
    (axisX K).conjTranspose = axisX K.conjTranspose := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [axisX, Matrix.conjTranspose_apply, h, eq_comm]

theorem axisY_conjTranspose (K : Matrix (Fin 10) (Fin 10) ℂ) :
    (axisY K).conjTranspose = axisY K.conjTranspose := by
  ext p q
  by_cases h : p.1 = q.1 <;> by_cases h' : p.2.2 = q.2.2 <;>
    simp [axisY, Matrix.conjTranspose_apply, h, h', eq_comm]

theorem axisZ_conjTranspose (K : Matrix (Fin 10) (Fin 10) ℂ) :
    (axisZ K).conjTranspose = axisZ K.conjTranspose := by
  ext p q
  by_cases h : p.1 = q.1 <;> by_cases h' : p.2.1 = q.2.1 <;>
    simp [axisZ, Matrix.conjTranspose_apply, h, h', eq_comm]

theorem axis_product_entry (X : Matrix (Fin 20) (Fin 20) ℂ)
    (Y Z : Matrix (Fin 10) (Fin 10) ℂ) (t : Cell → ℂ) (p q : Cell) :
    (axisZ Z * axisY Y * Matrix.diagonal t * axisX X) p q =
      Z p.2.2 q.2.2 * Y p.2.1 q.2.1 * t (p.1, q.2.1, q.2.2) * X p.1 q.1 := by
  simp [axisX, axisY, axisZ, Matrix.mul_apply, Matrix.diagonal,
    Fintype.sum_prod_type, ite_mul, mul_ite, ite_and]

def cyclicFourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun a b =>
  ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
    Complex.exp (Complex.I * ((-2 * Real.pi * (a.val : ℝ) * b.val / n : ℝ) : ℂ))

def fccTwiddle (p : Cell) : ℂ :=
  Complex.exp (Complex.I *
    ((2 * Real.pi * (p.1.val : ℝ) * (p.2.1.val + p.2.2.val) / 20 : ℝ) : ℂ))

def forwardFFT : Matrix Cell Cell ℂ :=
  axisZ (cyclicFourier 10) * axisY (cyclicFourier 10) *
    Matrix.diagonal fccTwiddle * axisX (cyclicFourier 20)

theorem normalization_factorization :
    (((Real.sqrt 10 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 10 : ℝ) : ℂ))⁻¹ *
      (((Real.sqrt 20 : ℝ) : ℂ))⁻¹ = normalization := by
  have hs : Real.sqrt 10 * Real.sqrt 10 * Real.sqrt 20 = Real.sqrt 2000 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10),
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10 * 10)]
    norm_num
  have hc := congrArg ((↑) : ℝ → ℂ) hs
  push_cast at hc
  unfold normalization
  rw [← hc]
  simp only [mul_inv]

theorem forwardFFT_eq_conjTranspose : forwardFFT = (transform 0).conjTranspose := by
  ext p q
  change (axisZ (cyclicFourier 10) * axisY (cyclicFourier 10) *
    Matrix.diagonal fccTwiddle * axisX (cyclicFourier 20)) p q = _
  rw [axis_product_entry]
  simp only [cyclicFourier, fccTwiddle, Matrix.conjTranspose_apply, transform, basis,
    star_mul, normalization, Complex.star_def, planeWave]
  rw [← Complex.exp_conj]
  have hphase :
      Complex.I * ((-2 * Real.pi * (p.2.2.val : ℝ) * q.2.2.val / 10 : ℝ) : ℂ) +
        Complex.I * ((-2 * Real.pi * (p.2.1.val : ℝ) * q.2.1.val / 10 : ℝ) : ℂ) +
        Complex.I * ((2 * Real.pi * (p.1.val : ℝ) * (q.2.1.val + q.2.2.val) / 20 : ℝ) : ℂ) +
        Complex.I * ((-2 * Real.pi * (p.1.val : ℝ) * q.1.val / 20 : ℝ) : ℂ) =
      star (Complex.I * (phase 0 p (representative q) : ℂ)) := by
    simp [phase, reciprocalIndex, representative, Fin.sum_univ_three]
    ring
  calc
    _ = (((Real.sqrt 10 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 10 : ℝ) : ℂ))⁻¹ *
        (((Real.sqrt 20 : ℝ) : ℂ))⁻¹ *
        (Complex.exp (Complex.I * ((-2 * Real.pi * (p.2.2.val : ℝ) * q.2.2.val / 10 : ℝ) : ℂ)) *
         Complex.exp (Complex.I * ((-2 * Real.pi * (p.2.1.val : ℝ) * q.2.1.val / 10 : ℝ) : ℂ)) *
         Complex.exp (Complex.I * ((2 * Real.pi * (p.1.val : ℝ) * (q.2.1.val + q.2.2.val) / 20 : ℝ) : ℂ)) *
         Complex.exp (Complex.I * ((-2 * Real.pi * (p.1.val : ℝ) * q.1.val / 20 : ℝ) : ℂ))) := by ring
    _ = _ := by
      rw [normalization_factorization, ← Complex.exp_add, ← Complex.exp_add,
        ← Complex.exp_add, hphase]
      simp [normalization, mul_comm]

def inverseFFT : Matrix Cell Cell ℂ :=
  (axisX (cyclicFourier 20)).conjTranspose * (Matrix.diagonal fccTwiddle).conjTranspose *
    (axisY (cyclicFourier 10)).conjTranspose * (axisZ (cyclicFourier 10)).conjTranspose

theorem inverseFFT_eq_transform : inverseFFT = transform 0 := by
  have h := congrArg Matrix.conjTranspose forwardFFT_eq_conjTranspose
  simpa only [forwardFFT, inverseFFT, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

end Maxwell.Certificate.FourierBinding
