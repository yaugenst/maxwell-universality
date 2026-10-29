import Maxwell.Continuum.FiberNormalizationBilinear

/-! Coordinatewise conjugation on the literal complex three-polarization
space and its infinite Hilbert sum. -/

noncomputable section
namespace Maxwell.Continuum.FiberNormalization

open FreeFiber

instance polarizationStar : Star Polarization where
  star v := WithLp.toLp 2 (fun j => star (v j))

@[simp] theorem polarization_star_apply (v : Polarization) (j : Fin 3) :
    star v j = star (v j) := rfl

instance polarizationStarAddMonoid : StarAddMonoid Polarization where
  star_involutive v := by
    apply PiLp.ext
    intro j
    simp only [polarization_star_apply, star_star]
  star_add v w := by
    apply PiLp.ext
    intro j
    change star (v j + w j) = star (v j) + star (w j)
    exact star_add _ _

instance polarizationNormedStarGroup : NormedStarGroup Polarization where
  norm_star_le v := by
    apply le_of_eq
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, polarization_star_apply, norm_star]

instance polarizationStarModule : StarModule ℂ Polarization where
  star_smul c v := by
    apply PiLp.ext
    intro j
    change star (c * v j) = star c * star (v j)
    exact star_mul' _ _

@[simp] theorem fiber_star_apply (v : FiberSpace) (ν : Alias) : star v ν = star (v ν) := rfl

end Maxwell.Continuum.FiberNormalization
