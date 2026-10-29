import Maxwell.Certificate.DyadicButterfly
import Maxwell.Certificate.DyadicFFT

/-! Bind checked mixed-radix lines to the actual FCC Fourier stage matrices. -/
namespace Maxwell.Certificate.DyadicButterflyFFT
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee
open DyadicButterfly

theorem axisXInverse_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 10 → Fin 10 → TwentyProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ y z, twentyNormalizedCheck p 1
      (fun j => input (j,y,z)) (w y z) (fun j => output (j,y,z)) = true) :
    DyadicFFT.Contains p output (axisX ((cyclicFourier 20).conjTranspose) *ᵥ v) := by
  intro r
  rw [axisX_mulVec]
  exact twentyInverse_sound (fun j => hv (j,r.2.1,r.2.2)) (h r.2.1 r.2.2) r.1

theorem axisXForward_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 10 → Fin 10 → TwentyProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ y z, twentyNormalizedCheck p (-1)
      (fun j => input (j,y,z)) (w y z) (fun j => output (j,y,z)) = true) :
    DyadicFFT.Contains p output (axisX ((cyclicFourier 20)) *ᵥ v) := by
  intro r
  rw [axisX_mulVec]
  exact twentyForward_sound (fun j => hv (j,r.2.1,r.2.2)) (h r.2.1 r.2.2) r.1

theorem axisYInverse_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 20 → Fin 10 → TenProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ x z, tenNormalizedCheck p 1
      (fun j => input (x,j,z)) (w x z) (fun j => output (x,j,z)) = true) :
    DyadicFFT.Contains p output (axisY ((cyclicFourier 10).conjTranspose) *ᵥ v) := by
  intro r
  rw [axisY_mulVec]
  exact tenInverse_sound (fun j => hv (r.1,j,r.2.2)) (h r.1 r.2.2) r.2.1

theorem axisYForward_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 20 → Fin 10 → TenProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ x z, tenNormalizedCheck p (-1)
      (fun j => input (x,j,z)) (w x z) (fun j => output (x,j,z)) = true) :
    DyadicFFT.Contains p output (axisY ((cyclicFourier 10)) *ᵥ v) := by
  intro r
  rw [axisY_mulVec]
  exact tenForward_sound (fun j => hv (r.1,j,r.2.2)) (h r.1 r.2.2) r.2.1

theorem axisZInverse_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 20 → Fin 10 → TenProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ x y, tenNormalizedCheck p 1
      (fun j => input (x,y,j)) (w x y) (fun j => output (x,y,j)) = true) :
    DyadicFFT.Contains p output (axisZ ((cyclicFourier 10).conjTranspose) *ᵥ v) := by
  intro r
  rw [axisZ_mulVec]
  exact tenInverse_sound (fun j => hv (r.1,r.2.1,j)) (h r.1 r.2.1) r.2.2

theorem axisZForward_sound {p : ℕ} {input output : DyadicFFT.Field}
    (w : Fin 20 → Fin 10 → TenProposal) {v : Cell → ℂ}
    (hv : DyadicFFT.Contains p input v)
    (h : ∀ x y, tenNormalizedCheck p (-1)
      (fun j => input (x,y,j)) (w x y) (fun j => output (x,y,j)) = true) :
    DyadicFFT.Contains p output (axisZ ((cyclicFourier 10)) *ᵥ v) := by
  intro r
  rw [axisZ_mulVec]
  exact tenForward_sound (fun j => hv (r.1,r.2.1,j)) (h r.1 r.2.1) r.2.2

theorem inverse_compose {p : ℕ} {input first second third result : DyadicFFT.Field}
    {v : Cell → ℂ} (hv : DyadicFFT.Contains p input v)
    (hZ : ∀ u, DyadicFFT.Contains p input u →
      DyadicFFT.Contains p first (axisZ (cyclicFourier 10).conjTranspose *ᵥ u))
    (hY : ∀ u, DyadicFFT.Contains p first u →
      DyadicFFT.Contains p second (axisY (cyclicFourier 10).conjTranspose *ᵥ u))
    (hT : DyadicFFT.diagonalCheck p 52 (DyadicFFT.conjugate FFTWitness.twiddle)
      second third = true)
    (hX : ∀ u, DyadicFFT.Contains p third u →
      DyadicFFT.Contains p result (axisX (cyclicFourier 20).conjTranspose *ᵥ u)) :
    DyadicFFT.Contains p result (transform 0 *ᵥ v) := by
  have h1 := hZ _ hv
  have h2 := hY _ h1
  have h3 := DyadicFFT.diagonalCheck_sound
    (DyadicFFT.conjugate_contains FFTWitness.twiddle_contains) h2 hT
  have h4 := hX _ h3
  rw [← inverseFFT_eq_transform, inverseFFT, axisX_conjTranspose, axisY_conjTranspose,
    axisZ_conjTranspose, Matrix.diagonal_conjTranspose]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

theorem forward_compose {p : ℕ} {input first second third result : DyadicFFT.Field}
    {v : Cell → ℂ} (hv : DyadicFFT.Contains p input v)
    (hX : ∀ u, DyadicFFT.Contains p input u →
      DyadicFFT.Contains p first (axisX (cyclicFourier 20) *ᵥ u))
    (hT : DyadicFFT.diagonalCheck p 52 FFTWitness.twiddle first second = true)
    (hY : ∀ u, DyadicFFT.Contains p second u →
      DyadicFFT.Contains p third (axisY (cyclicFourier 10) *ᵥ u))
    (hZ : ∀ u, DyadicFFT.Contains p third u →
      DyadicFFT.Contains p result (axisZ (cyclicFourier 10) *ᵥ u)) :
    DyadicFFT.Contains p result ((transform 0).conjTranspose *ᵥ v) := by
  have h1 := hX _ hv
  have h2 := DyadicFFT.diagonalCheck_sound FFTWitness.twiddle_contains h1 hT
  have h3 := hY _ h2
  have h4 := hZ _ h3
  rw [← forwardFFT_eq_conjTranspose, forwardFFT]
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4

theorem tenNormalizedCheck_transfer {p : ℕ} {sign : ℤ}
    {a b a' b' : Values 10} {w : TenProposal}
    (ha : a' = a) (hb : b' = b)
    (h : tenNormalizedCheck p sign a' w b' = true) :
    tenNormalizedCheck p sign a w b = true := by
  subst a' b'
  exact h

theorem twentyNormalizedCheck_transfer {p : ℕ} {sign : ℤ}
    {a b a' b' : Values 20} {w : TwentyProposal}
    (ha : a' = a) (hb : b' = b)
    (h : twentyNormalizedCheck p sign a' w b' = true) :
    twentyNormalizedCheck p sign a w b = true := by
  subst a' b'
  exact h

end Maxwell.Certificate.DyadicButterflyFFT
