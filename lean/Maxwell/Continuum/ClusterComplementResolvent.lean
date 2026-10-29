import Maxwell.Continuum.ClusterComplementResolventBasic

/-!
# Two-sided inverse of the full continuum fiber

Invertibility of the literal finite Schur operator gives a bounded
inverse on the actual maximal domain of the complete infinite fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber SelfAdjointResolvent

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)

theorem fullResolvent_right (J : clusterSpace →L[ℂ] clusterSpace)
    (hJ : finiteSchur t e ht he * J = 1) (f : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨fullResolvent t e ht he J f,fullResolvent_mem_domain t e ht he J f⟩ = f := by
  have hs0 : finiteSchur t e ht he (J (adjustedSource t e ht he f)) = adjustedSource t e ht he f :=
    congrArg (fun T : clusterSpace →L[ℂ] clusterSpace => T (adjustedSource t e ht he f)) hJ
  have hs : effectiveSchur t e ht he (J (adjustedSource t e ht he f)).val =
      (adjustedSource t e ht he f).val := congrArg Subtype.val hs0
  change (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun
    ((⟨complementInverse t e ht he f,complementInverse_mem_domain t e ht he f⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) +
      (backgroundAmplitude : ℂ)⁻¹ •
      ⟨schurLift t e ht he (J (adjustedSource t e ht he f)).val,schurLift_mem_domain t e ht he _⟩) = f
  rw [map_add,map_smul]
  change materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨complementInverse t e ht he f,complementInverse_mem_domain t e ht he f⟩ +
    (backgroundAmplitude : ℂ)⁻¹ • materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he (J (adjustedSource t e ht he f)).val,schurLift_mem_domain t e ht he _⟩ = f
  rw [schurLift_residual,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'),one_smul,
    hs,adjustedSource_apply,complementInverse_full_residual]
  change (f - clusterProjection f) + _ + (clusterProjection f - _) = f
  abel

theorem materialFiber_injective_of_schur
    (hS : Function.Injective (finiteSchur t e ht he)) :
    Function.Injective (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) := by
  have hz (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
      (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) : u = 0 := by
    have hp : finiteSchur t e ht he (clusterProjectionToSpace u.val) = 0 := by
      apply Subtype.ext
      exact kernel_projects_to_schur t e ht he u hu
    have hp0 : clusterProjectionToSpace u.val = 0 := hS (hp.trans (map_zero _).symm)
    have hP : clusterProjection u.val = 0 := congrArg Subtype.val hp0
    have hr := kernel_reconstruction t e ht he u hu
    rw [← schurLift_clusterProjection t e ht he u.val,hP,map_zero] at hr
    exact Subtype.ext hr.symm
  intro u v huv
  apply sub_eq_zero.mp
  apply hz
  change (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun (u-v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr huv

/-- Explicit two-sided inverse from any literal finite inverse. -/
def inverseFromFinite (J : clusterSpace →L[ℂ] clusterSpace)
    (hJright : finiteSchur t e ht he * J = 1) (hJleft : J * finiteSchur t e ht he = 1) :
    BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) where
  map := fullResolvent t e ht he J
  mem_domain := fullResolvent_mem_domain t e ht he J
  apply_map := fullResolvent_right t e ht he J hJright
  map_apply u := by
    have hS : Function.Injective (finiteSchur t e ht he) := by
      intro x y hxy
      have hleft (x : clusterSpace) : J (finiteSchur t e ht he x) = x :=
        congrArg (fun T : clusterSpace →L[ℂ] clusterSpace => T x) hJleft
      have h := congrArg J hxy
      rwa [hleft,hleft] at h
    have hh := materialFiber_injective_of_schur t e ht he hS
      (fullResolvent_right t e ht he J hJright
        (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u))
    exact congrArg Subtype.val hh

/-- Canonical full inverse obtained from the actual finite Schur unit. -/
def inverseFromSchur (hS : IsUnit (finiteSchur t e ht he)) :
    BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) :=
  inverseFromFinite t e ht he (Ring.inverse (finiteSchur t e ht he))
    (Ring.mul_inverse_cancel _ hS) (Ring.inverse_mul_cancel _ hS)

theorem inverseFromSchur_norm_le (hS : IsUnit (finiteSchur t e ht he)) :
    ‖(inverseFromSchur t e ht he hS).map‖ ≤
      2 + 4 * backgroundAmplitude⁻¹ * ‖Ring.inverse (finiteSchur t e ht he)‖ :=
  fullResolvent_norm_le t e ht he _

end Maxwell.Continuum.ClusterComplement
