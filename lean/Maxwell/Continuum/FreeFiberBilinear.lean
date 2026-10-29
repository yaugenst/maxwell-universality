import Maxwell.Continuum.PeriodicBandProjection
import Maxwell.Continuum.FiberNormalizationConjugation

/-! The complex fiber is symmetric for the actual complex bilinear
Fourier pairing. This uses transpose symmetry of all Maxwell blocks and
the literal scalar convolution potential, not Hermitian symmetry at
complex momentum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FreeFiber

open FiberNormalization

theorem polarization_bilinear (u v : Polarization) :
    bilinear u v = ∑ j, u j * v j := by
  simp only [bilinear_apply, PiLp.inner_apply, RCLike.inner_apply', polarization_star_apply,
    RCLike.star_def, starRingEnd_self_apply]

theorem block_bilinear_symmetric (p : Momentum) (E : ℂ) (u v : Polarization) :
    bilinear (block p E u) v = bilinear u (block p E v) := by
  simp only [polarization_bilinear, FiberReflection.block_coordinate, bilinearDot,
    Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  ring

theorem operator_bilinear_symmetric (q : Momentum) (E : ℂ)
    (u v : (operator q E).domain) :
    bilinear (operator q E u) v.val = bilinear u.val (operator q E v) := by
  rw [bilinear_apply, bilinear_apply, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro ν
  exact block_bilinear_symmetric (aliasMomentum q ν) E (u.val ν) (v.val ν)

theorem potential_bilinear_symmetric (u v : FiberSpace) :
    bilinear (potential u) v = bilinear u (potential v) := by
  rw [bilinear_apply, bilinear_apply, potential_star]
  exact potential_isSymmetric (star u) v

theorem material_bilinear_symmetric (q : Momentum) (E : ℂ) (ρ : ℝ)
    (u v : (materialFiber q E ρ).domain) :
    bilinear (materialFiber q E ρ u) v.val = bilinear u.val (materialFiber q E ρ v) := by
  rw [materialFiber_apply, materialFiber_apply]
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
  rw [operator_bilinear_symmetric, potential_bilinear_symmetric]

theorem inverse_bilinear_symmetric (q : Momentum) (E : ℂ) (ρ : ℝ)
    (R : SelfAdjointResolvent.BoundedInverse (materialFiber q E ρ)) (u v : FiberSpace) :
    bilinear (R.map u) v = bilinear u (R.map v) := by
  have h := material_bilinear_symmetric q E ρ
    ⟨R.map u, R.mem_domain u⟩ ⟨R.map v, R.mem_domain v⟩
  rw [R.apply_map, R.apply_map] at h
  exact h.symm

end Maxwell.Continuum.FreeFiber
