import Maxwell.Continuum.FiberL1Coupling

/-!
# Absolute Fourier summability of actual cell eigenvectors

Every kernel vector of the literal infinite material fiber belongs to ℓ¹.
This follows from the finite central cluster, the actual off-diagonal block,
and the complement inverse on ℓ¹, identified with the Hilbert-space inverse.
No regularity or summability premise is imposed on the eigenvector.
-/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber ClusterComplement

set_option backward.isDefEq.respectTransparency false

theorem kernel_schurLift_inclusion (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    inclusion (schurLift t e ht he u.val) = u.val := by
  rw [inclusion_schurLift, ClusterComplement.kernel_reconstruction t e ht he u hu]

theorem kernel_schurLift_coefficient (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0)
    (ν : Alias) : schurLift t e ht he u.val ν = u.val ν :=
  congrArg (fun v : FiberSpace => v ν) (kernel_schurLift_inclusion t e ht he u hu)

theorem kernel_memℓ1 (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    Memℓp (fun ν => u.val ν) 1 := by
  have h := lp.memℓp (schurLift t e ht he u.val)
  change Memℓp (fun ν => schurLift t e ht he u.val ν) 1 at h
  have hf : (fun ν => schurLift t e ht he u.val ν) = fun ν => u.val ν :=
    funext (kernel_schurLift_coefficient t e ht he u hu)
  rwa [hf] at h

theorem kernel_summable_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    Summable (fun ν => ‖u.val ν‖) := by
  simpa only [kernel_schurLift_coefficient t e ht he u hu] using
    summable_norm (schurLift t e ht he u.val)

theorem kernel_fourier_l1_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    ∑' ν, ‖u.val ν‖ ≤ 9 * ‖ClusterComplement.clusterProjection u.val‖ := by
  have h := schurLift_norm_le t e ht he u.val
  rw [norm_eq_tsum] at h
  simpa only [kernel_schurLift_coefficient t e ht he u hu] using h

/-- The paper's uniform bound follows even from normalization of the central
cluster alone; the complementary coefficients are all included in the sum. -/
theorem kernel_fourier_l1_bound_of_cluster (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0)
    (hnorm : ‖ClusterComplement.clusterProjection u.val‖ ≤ 1) :
    Summable (fun ν => ‖u.val ν‖) ∧ ∑' ν, ‖u.val ν‖ ≤ 32 := by
  refine ⟨kernel_summable_norm t e ht he u hu, ?_⟩
  nlinarith [kernel_fourier_l1_le t e ht he u hu]

/-- Every normalized actual Maxwell fiber eigenvector has absolutely summable
Fourier coefficients, uniformly bounded by 32 throughout the complex box. -/
theorem kernel_fourier_l1_bound (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0)
    (hnorm : ‖u.val‖ ≤ 1) :
    Summable (fun ν => ‖u.val ν‖) ∧ ∑' ν, ‖u.val ν‖ ≤ 32 := by
  apply kernel_fourier_l1_bound_of_cluster t e ht he u hu
  exact ((ClusterComplement.clusterProjection.le_opNorm u.val).trans
    ((mul_le_mul_of_nonneg_right ClusterComplement.clusterProjection_norm_le
      (norm_nonneg u.val)).trans_eq (one_mul _))).trans hnorm

#print axioms kernel_memℓ1
#print axioms kernel_fourier_l1_le
#print axioms kernel_fourier_l1_bound_of_cluster
#print axioms kernel_fourier_l1_bound

end Maxwell.Continuum.FiberL1
