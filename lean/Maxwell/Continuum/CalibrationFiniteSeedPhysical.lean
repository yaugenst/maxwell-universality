import Maxwell.Continuum.CalibrationFinitePrecision
import Maxwell.Continuum.CalibrationFiniteOperator
import Maxwell.Continuum.CalibrationSeedNorm

/-! The computed finite starting vector approximates the actual physical
starting envelope after its proved nonzero normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber Supercell EffectiveMass NormedSpace MasterConstants

attribute [local irreducible] size precision rootBits workPrecision seed rawSeed
  embedding exactRootSeed startingVector

private theorem physical_seed_transport (M : ℕ) [NeZero M]
    (v w : FourierData) (u : FiberSpace) (a : FieldL2) {ε : ℝ}
    (hv : v=w) (he : ‖w.value-normalize u‖≤ε)
    (hu : embedding M (normalize u)=a) : ‖embedding M v.value-a‖≤ε := by
  rw [hv,← hu,← map_sub,embedding_norm]
  exact he

theorem seed_eq (L r N : ℕ) : seed L r N =
    FourierData.normalizeData (precision L r N)
      (FourierData.rootApply (scale L r N) (precision L r N) (rootBits L r N)
        (finiteSeed (size L r N) (precision L r N))) := by
  unfold seed rawSeed
  rfl


theorem seed_physical_error {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) :
    ‖embedding (size L r N) (seed L r N).value-startingVector (inverse_length_pos hL)‖ ≤
      (1/2 : ℝ)^workPrecision N := by
  have hL0 : 0<L := by exact_mod_cast length_pos hL
  have hs := scale_lower hL0 r N
  have hl := exactRootSeed_norm_lower (size L r N) hL (size_even L r N)
    (size_well_geometry L r N) (scale L r N) hs (scale_cast L r N)
    (rootBits L r N) (scale_bound hL0 r N)
  have he := finiteRootSeed_normalized_error (size L r N) (scale L r N) hs
    (precision L r N) (rootBits L r N) (scale_bound hL0 r N)
    (by positivity : 0<(1/2 : ℝ)^(39+2*rootBits L r N)) hl (seed_normalize_small L r N)
  have hp := exactRootSeed_normalize (size L r N) hL (size_even L r N)
    (size_well_geometry L r N) (scale L r N) hs (scale_cast L r N)
  exact (physical_seed_transport (size L r N) (seed L r N) _ _ _ (seed_eq L r N) he hp).trans
    (seed_normalize_budget L r N)

#print axioms seed_physical_error

end Maxwell.Continuum.Calibration.FiniteAlgorithm
