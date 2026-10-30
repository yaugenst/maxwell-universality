import Maxwell.Continuum.CompactTemplateField

/-! Exact rational rescaling from physical Fourier frequencies to the unit template. -/

namespace Maxwell.Continuum.Profile

def scaleFrequency (L : ℚ) (q : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => L*q i

theorem spatialPlaneWave_scale (L : ℚ) (hL : L≠0) (q : Fin 3 → ℚ) (x : Fin 3 → ℝ) :
    spatialPlaneWave (scaleFrequency L q) (fun i => (L : ℝ)⁻¹*x i)=spatialPlaneWave q x := by
  unfold spatialPlaneWave
  congr 4
  apply Finset.sum_congr rfl
  intro i _
  have hLr : (L : ℝ)≠0 := Rat.cast_ne_zero.mpr hL
  simp only [scaleFrequency,Rat.cast_mul]
  field_simp

theorem finiteFourier_scale {ι : Type*} {B : ℕ} (s : Finset ι)
    (L : ℚ) (hL : L≠0) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B) (x : Fin 3 → ℝ) :
    finiteFourier s (fun ν => scaleFrequency L (q ν)) a (fun i => (L : ℝ)⁻¹*x i)=finiteFourier s q a x := by
  simp only [finiteFourier,spatialPlaneWave_scale L hL]

theorem idealPlacedTemplate_physical {ι : Type*} {B : ℕ} (s : Finset ι)
    (L : ℚ) (hL : L≠0) (q : ι → Fin 3 → ℚ) (a : ι → ComplexDyadic B) (r x : Space) :
    idealPlacedTemplate s (fun ν => scaleFrequency L (q ν)) a (L : ℝ) r x=
      (Well.qw ((L : ℝ)⁻¹ • (x-r)) : ℂ)*finiteFourier s q a (fun i => (x-r) i) := by
  unfold idealPlacedTemplate idealFiniteTemplate
  congr 1
  change finiteFourier s (fun ν => scaleFrequency L (q ν)) a
    (fun i => (L : ℝ)⁻¹*(x-r) i)=_
  exact finiteFourier_scale s L hL q a _

theorem scaleFrequency_bound (L : ℚ) (q : Fin 3 → ℚ) (Q R : ℕ)
    (hL : |L|≤R) (hq : ∀ i, |q i|≤Q) : ∀ i, |scaleFrequency L q i|≤(R*Q : ℕ) := by
  intro i
  rw [scaleFrequency, abs_mul, Nat.cast_mul]
  exact mul_le_mul hL (hq i) (abs_nonneg _) (Nat.cast_nonneg _)

#print axioms idealPlacedTemplate_physical

end Maxwell.Continuum.Profile
