import Maxwell.Continuum.CalibrationRationalMaps
import Maxwell.Continuum.CalibrationRationalSchur

/-! The real and complex rational Schur evaluators use the same arithmetic.
Mapping scalar coefficients commutes with every finite recurrence step. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem rationalInverseApply_map (L : V →ₗ[ℚ] W) (t E : ℚ) (r : Fin 3 → ℚ)
    (f : Alias → Fin 3 → V) (K : ℕ) :
    rationalInverseApply t E r (rationalMap L f) K = rationalMap L (rationalInverseApply t E r f K) := by
  induction K with
  | zero => funext ν j; exact (map_zero L).symm
  | succ K ih =>
    simp only [rationalInverseApply, ih, rationalPerturbation_map, rationalFreeApply_map]
    funext ν j
    exact (map_sub L _ _).symm

theorem rationalCentral_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalCentral (rationalMap L f) = rationalMap L (rationalCentral f) := by
  funext ν j
  unfold rationalCentral rationalMap
  split_ifs with h <;> simp only [h, Bool.false_eq_true, ↓reduceIte, map_zero]

theorem rationalCentralApply_map (L : V →ₗ[ℚ] W) (t E : ℚ) (r : Fin 3 → ℚ)
    (f : Alias → Fin 3 → V) :
    rationalCentralApply t E r (rationalMap L f) = rationalMap L (rationalCentralApply t E r f) := by
  funext ν j
  unfold rationalCentralApply rationalMap
  split_ifs with h <;> simp only [h, Bool.false_eq_true, ↓reduceIte, map_zero, map_sum, map_smul]

theorem rationalCentralMaterial_map (L : V →ₗ[ℚ] W) (t E : ℚ) (r : Fin 3 → ℚ)
    (f : Alias → Fin 3 → V) :
    rationalCentralMaterial t E r (rationalMap L f) = rationalMap L (rationalCentralMaterial t E r f) := by
  unfold rationalCentralMaterial
  rw [rationalCentralApply_map, rationalCentral_map, rationalPotential_map, rationalCentral_map]
  funext ν j
  exact (by simp only [rationalMap, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul])

theorem rationalRightCoupling_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalRightCoupling (rationalMap L f) = rationalMap L (rationalRightCoupling f) := by
  unfold rationalRightCoupling
  rw [rationalCentral_map, rationalPotential_map, rationalNoncentral_map]
  funext ν j
  exact (L.map_smul _ _).symm

theorem rationalLeftCoupling_map (L : V →ₗ[ℚ] W) (f : Alias → Fin 3 → V) :
    rationalLeftCoupling (rationalMap L f) = rationalMap L (rationalLeftCoupling f) := by
  unfold rationalLeftCoupling
  rw [rationalNoncentral_map, rationalPotential_map, rationalCentral_map]
  funext ν j
  exact (L.map_smul _ _).symm

theorem rationalSchurApply_map (L : V →ₗ[ℚ] W) (t E : ℚ) (r : Fin 3 → ℚ)
    (f : Alias → Fin 3 → V) (K : ℕ) :
    rationalSchurApply t E r K (rationalMap L f) = rationalMap L (rationalSchurApply t E r K f) := by
  unfold rationalSchurApply
  rw [rationalCentralMaterial_map, rationalRightCoupling_map, rationalNoncentral_map,
    rationalInverseApply_map, rationalLeftCoupling_map]
  funext ν j
  exact (map_sub L _ _).symm

end Maxwell.Continuum.Calibration
