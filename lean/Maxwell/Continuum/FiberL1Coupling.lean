import Maxwell.Continuum.FiberL1Cluster
import Maxwell.Continuum.ClusterComplementLift

/-! The actual off-diagonal fiber coupling and Schur lift preserve absolute
summability. The inclusion into the Hilbert fiber intertwines both maps. -/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber ClusterComplement

set_option backward.isDefEq.respectTransparency false

def freeRightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : Space →L[ℂ] Space :=
  blockMultiplier (ClusterComplement.freeRightCouplingBlock t E)
    (div_nonneg backgroundAmplitude_pos.le (by norm_num))
    (ClusterComplement.freeRightCouplingBlock_norm_le t E ht)

theorem freeRightCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖freeRightCoupling t E ht‖ ≤ backgroundAmplitude / 32 :=
  blockMultiplier_norm_le _ _ _

theorem inclusion_freeRightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : Space) :
    inclusion (freeRightCoupling t E ht u) =
      ClusterComplement.freeRightCoupling t E ht (inclusion u) := rfl

def rightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : Space →L[ℂ] Space :=
  freeRightCoupling t E ht - (backgroundAmplitude : ℂ) •
    (complementProjection * potential * clusterProjection)

theorem rightCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖rightCoupling t E ht‖ ≤ 8 * backgroundAmplitude := by
  have hp := (contraction_sandwich_norm_le complementProjection potential clusterProjection
    complementProjection_norm_le clusterProjection_norm_le).trans potential_norm_le
  have h := norm_sub_le (freeRightCoupling t E ht)
    ((backgroundAmplitude : ℂ) • (complementProjection * potential * clusterProjection))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos] at h
  unfold rightCoupling
  nlinarith [freeRightCoupling_norm_le t E ht,
    mul_le_mul_of_nonneg_left hp backgroundAmplitude_pos.le, backgroundAmplitude_pos]

theorem inclusion_rightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : Space) :
    inclusion (rightCoupling t E ht u) =
      ClusterComplement.rightCoupling t E ht (inclusion u) := by
  change inclusion (freeRightCoupling t E ht u - (backgroundAmplitude : ℂ) •
    complementProjection (potential (clusterProjection u))) =
    ClusterComplement.freeRightCoupling t E ht (inclusion u) - (backgroundAmplitude : ℂ) •
    ClusterComplement.complementProjection
      (FreeFiber.potential (ClusterComplement.clusterProjection (inclusion u)))
  rw [map_sub, map_smul, inclusion_freeRightCoupling, inclusion_complementProjection,
    inclusion_potential, inclusion_clusterProjection]

def schurLift (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : FiberSpace →L[ℂ] Space :=
  clusterLift - (complementInverse t e ht he * rightCoupling t (totalEnergy e) ht).comp clusterLift

theorem inclusion_schurLift (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    inclusion (schurLift t e ht he u) = ClusterComplement.schurLift t e ht he u := by
  change inclusion (clusterLift u - complementInverse t e ht he
    (rightCoupling t (totalEnergy e) ht (clusterLift u))) =
    ClusterComplement.clusterProjection u - ClusterComplement.complementInverse t e ht he
      (ClusterComplement.rightCoupling t (totalEnergy e) ht u)
  rw [map_sub, inclusion_clusterLift, inclusion_complementInverse, inclusion_rightCoupling,
    inclusion_clusterLift, ClusterComplement.rightCoupling_clusterProjection]

theorem schurLift_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    ‖schurLift t e ht he u‖ ≤ 9 * ‖ClusterComplement.clusterProjection u‖ := by
  have hR := (complementInverse t e ht he).le_opNorm
    (rightCoupling t (totalEnergy e) ht (clusterLift u))
  have hB := (rightCoupling t (totalEnergy e) ht).le_opNorm (clusterLift u)
  have hRB : ‖complementInverse t e ht he (rightCoupling t (totalEnergy e) ht (clusterLift u))‖ ≤
      2 * (8 * backgroundAmplitude) * ‖clusterLift u‖ := by
    calc
      _ ≤ 2 * ‖rightCoupling t (totalEnergy e) ht (clusterLift u)‖ :=
        hR.trans (mul_le_mul_of_nonneg_right (complementInverse_norm_le t e ht he) (norm_nonneg _))
      _ ≤ 2 * ((8 * backgroundAmplitude) * ‖clusterLift u‖) :=
        mul_le_mul_of_nonneg_left
          (hB.trans (mul_le_mul_of_nonneg_right (rightCoupling_norm_le t (totalEnergy e) ht)
            (norm_nonneg _))) (by norm_num)
      _ = _ := by ring
  change ‖clusterLift u - complementInverse t e ht he
    (rightCoupling t (totalEnergy e) ht (clusterLift u))‖ ≤ _
  have h := norm_sub_le (clusterLift u)
    (complementInverse t e ht he (rightCoupling t (totalEnergy e) ht (clusterLift u)))
  have hρ : 2 * (8 * backgroundAmplitude) ≤ (1 : ℝ) / 8 := by
    nlinarith [backgroundAmplitude_le]
  have hsmall := mul_le_mul_of_nonneg_right hρ (norm_nonneg (clusterLift u))
  nlinarith [clusterLift_norm_le_projection u]

#print axioms inclusion_schurLift
#print axioms schurLift_norm_le

end Maxwell.Continuum.FiberL1
