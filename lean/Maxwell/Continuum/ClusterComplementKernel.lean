import Maxwell.Continuum.ClusterComplementFinite

/-!
# Exact kernel equivalence for the continuum Schur reduction

The sixteen-dimensional Schur kernel is linearly equivalent to the kernel
of the actual infinite Maxwell fiber on its maximal domain.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

abbrev ActualKernel (t : Momentum) (e : ℂ) :=
  LinearMap.ker (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun

abbrev FiniteKernel (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :=
  LinearMap.ker (finiteSchur t e ht he).toLinearMap

theorem finiteKernel_equation (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : FiniteKernel t e ht he) : effectiveSchur t e ht he u.val.val = 0 := by
  have h : finiteSchur t e ht he u.val = 0 := u.property
  exact congrArg Subtype.val h

def fiberSchurKernelEquiv (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    FiniteKernel t e ht he ≃ₗ[ℂ] ActualKernel t e where
  toFun u := ⟨⟨schurLift t e ht he u.val.val, schurLift_mem_domain t e ht he u.val.val⟩,
    schur_kernel_lifts t e ht he u.val.val (finiteKernel_equation t e ht he u)⟩
  invFun u := ⟨⟨clusterProjection u.val.val,
    (mem_clusterSpace_iff _).mpr (clusterProjection_idempotent u.val.val)⟩, by
      change finiteSchur t e ht he _ = 0
      apply Subtype.ext
      exact kernel_projects_to_schur t e ht he u.val u.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact (clusterProjection_schurLift t e ht he u.val.val).trans
      ((mem_clusterSpace_iff _).mp u.val.property)
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact (schurLift_clusterProjection t e ht he u.val.val).trans
      (kernel_reconstruction t e ht he u.val u.property)
  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (schurLift t e ht he).map_add u.val.val v.val.val
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    exact (schurLift t e ht he).map_smul c u.val.val

theorem actualKernel_finrank_eq (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    Module.finrank ℂ (ActualKernel t e) = Module.finrank ℂ (FiniteKernel t e ht he) :=
  (fiberSchurKernelEquiv t e ht he).finrank_eq.symm

end Maxwell.Continuum.ClusterComplement
