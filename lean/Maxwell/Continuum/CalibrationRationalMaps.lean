import Maxwell.Continuum.CalibrationRationalStencil

/-! Naturality of the executable rational stencil. The identical
arithmetic handles real matrix columns and complex Fourier vectors. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable {V W : Type*} [AddCommMonoid V] [Module ℚ V] [AddCommMonoid W] [Module ℚ W]

def rationalMap (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) : Alias → Fin 3 → W :=
  fun ν j => L (f ν j)

theorem rationalNoncentral_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalNoncentral (rationalMap L f) = rationalMap L (rationalNoncentral f) := by
  funext ν j
  unfold rationalNoncentral rationalMap
  split_ifs with h <;> simp only [h, Bool.false_eq_true, ↓reduceIte, map_zero]

theorem rationalPotential_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalPotential (rationalMap L f) = rationalMap L (rationalPotential f) := by
  funext ν j
  simp only [rationalPotential, rationalMap, map_sum, map_smul, map_add]

theorem rationalPerturbation_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalPerturbation (rationalMap L f) = rationalMap L (rationalPerturbation f) := by
  unfold rationalPerturbation
  rw [rationalNoncentral_map, rationalPotential_map, rationalNoncentral_map]
  funext ν j
  exact (L.map_smul _ _).symm

theorem rationalFreeApply_map (L : V →ₗ[ℚ] W) (t E : ℚ) (r : Fin 3 → ℚ) (f : Alias → Fin 3 → V) :
    rationalFreeApply t E r (rationalMap L f) = rationalMap L (rationalFreeApply t E r f) := by
  funext ν j
  simp only [rationalFreeApply, rationalMap, map_sum, map_smul]

end Maxwell.Continuum.Calibration
