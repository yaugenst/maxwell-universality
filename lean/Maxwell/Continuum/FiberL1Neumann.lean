import Maxwell.Continuum.FiberL1Complement

/-!
# The actual complementary Neumann inverse preserves absolute summability

The Banach-space geometric series uses the literal free inverse blocks and
compressed six-neighbor potential. Its inclusion into ℓ² is proved equal to
the existing inverse of the actual complementary Maxwell fiber.
-/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber ClusterComplement

set_option backward.isDefEq.respectTransparency false

def series (T : Space →L[ℂ] Space) : Space →L[ℂ] Space := ∑' n : ℕ, T ^ n

theorem series_left (T : Space →L[ℂ] Space) (hT : ‖T‖ < 1) (u : Space) :
    series T u - T (series T u) = u :=
  congrArg (fun L : Space →L[ℂ] Space => L u) (mul_neg_geom_series T hT)

theorem series_norm_le (T : Space →L[ℂ] Space) (hT : ‖T‖ < 1) :
    ‖series T‖ ≤ (1 - ‖T‖)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one T hT
  have hone : ‖(1 : Space →L[ℂ] Space)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖series T‖ ≤ _ at h
  linarith

/-- Equality follows from the two genuine geometric-series inverse laws. -/
theorem inclusion_series (T : Space →L[ℂ] Space) (S : FiberSpace →L[ℂ] FiberSpace)
    (hT : ‖T‖ < 1) (hS : ‖S‖ < 1)
    (hTS : ∀ u, inclusion (T u) = S (inclusion u)) (u : Space) :
    inclusion (series T u) = Neumann.series S (inclusion u) := by
  have hleft := congrArg inclusion (series_left T hT u)
  rw [map_sub, hTS] at hleft
  have hright := Neumann.series_right S hS (inclusion (series T u))
  rw [hleft] at hright
  exact hright.symm

def materialInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : Space →L[ℂ] Space :=
  freeInverse t e ht he * series (-(materialPart * freeInverse t e ht he))

theorem materialInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖materialInverse t e ht he‖ ≤ 2 := by
  have hs := materialPart_inverse_product_norm t e ht he
  have hsmall : ‖-(materialPart * freeInverse t e ht he)‖ < 1 := by
    rw [norm_neg]
    linarith
  have hden : 0 < 1 - ‖materialPart * freeInverse t e ht he‖ := by linarith
  have hinv : (1 - ‖materialPart * freeInverse t e ht he‖)⁻¹ ≤ (4 / 3 : ℝ) := by
    have h := (inv_le_inv₀ hden (by norm_num : (0 : ℝ) < 3 / 4)).mpr (by linarith)
    norm_num at h
    exact h
  have hseries : ‖series (-(materialPart * freeInverse t e ht he))‖ ≤ 4 / 3 :=
    (series_norm_le _ hsmall).trans (by simpa only [norm_neg] using hinv)
  exact (norm_mul_le _ _).trans ((mul_le_mul (freeInverse_norm_le t e ht he)
    hseries (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem inclusion_materialInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : Space) :
    inclusion (materialInverse t e ht he u) =
      (regularizedMaterialInverse t e ht he).map (inclusion u) := by
  change inclusion (freeInverse t e ht he (series (-(materialPart * freeInverse t e ht he)) u)) =
    (regularizedFreeInverse t e ht he).map
      (Neumann.series (-(compressedMaterial * (regularizedFreeInverse t e ht he).map)) (inclusion u))
  rw [inclusion_freeInverse]
  congr 1
  apply inclusion_series
  · rw [norm_neg]
    exact (materialPart_inverse_product_norm t e ht he).trans_lt (by norm_num)
  · rw [norm_neg]
    exact (compressedMaterial_inverse_product_norm t e ht he).trans_lt (by norm_num)
  · intro v
    change inclusion (-(materialPart (freeInverse t e ht he v))) =
      -(compressedMaterial ((regularizedFreeInverse t e ht he).map (inclusion v)))
    rw [map_neg, inclusion_materialPart, inclusion_freeInverse]

def complementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : Space →L[ℂ] Space :=
  materialInverse t e ht he * complementProjection

theorem complementInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖complementInverse t e ht he‖ ≤ 2 :=
  (norm_mul_le _ _).trans ((mul_le_mul (materialInverse_norm_le t e ht he)
    complementProjection_norm_le (norm_nonneg _) (by norm_num)).trans (by norm_num))

/-- This is a lift of the existing actual-domain inverse, including the
central longitudinal modes and every noncentral alias. -/
theorem inclusion_complementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : Space) :
    inclusion (complementInverse t e ht he u) =
      ClusterComplement.complementInverse t e ht he (inclusion u) := by
  change inclusion (materialInverse t e ht he (complementProjection u)) =
    (regularizedMaterialInverse t e ht he).map
      (ClusterComplement.complementProjection (inclusion u))
  rw [inclusion_materialInverse, inclusion_complementProjection]

theorem complementInverse_mem_actual_domain (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : Space) :
    inclusion (complementInverse t e ht he u) ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain := by
  rw [inclusion_complementInverse]
  exact ClusterComplement.complementInverse_mem_domain t e ht he (inclusion u)

#print axioms inclusion_complementInverse
#print axioms complementInverse_norm_le

end Maxwell.Continuum.FiberL1
