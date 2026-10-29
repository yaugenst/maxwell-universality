import Maxwell.Continuum.ClusterComplementResolvent

/-! Exact equivalence of finite Schur and full continuum bounded resolvents. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber SelfAdjointResolvent

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)

/-- A bounded inverse for the full maximal-domain operator forces the finite
Schur operator to be a genuine unit. -/
theorem schur_isUnit_of_inverse
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    IsUnit (finiteSchur t e ht he) := by
  have hz (u : clusterSpace) (hu : finiteSchur t e ht he u = 0) : u = 0 := by
    have heff : effectiveSchur t e ht he u.val = 0 := congrArg Subtype.val hu
    have hM := schur_kernel_lifts t e ht he u.val heff
    have hR := R.map_apply ⟨schurLift t e ht he u.val,schurLift_mem_domain t e ht he u.val⟩
    rw [hM,map_zero] at hR
    change 0 = schurLift t e ht he u.val at hR
    have hP := clusterProjection_schurLift t e ht he u.val
    rw [← hR,map_zero,(mem_clusterSpace_iff _).mp u.property] at hP
    exact Subtype.ext hP.symm
  have hinj : Function.Injective (finiteSchur t e ht he).toLinearMap := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩

/-- No domain, missing-alias or coupling hypothesis remains in this equivalence. -/
theorem boundedInverse_nonempty_iff_schur_isUnit :
    Nonempty (BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) ↔
      IsUnit (finiteSchur t e ht he) :=
  ⟨fun ⟨R⟩ => schur_isUnit_of_inverse t e ht he R,
    fun hS => ⟨inverseFromSchur t e ht he hS⟩⟩

theorem inverseFromFinite_norm_le (J : clusterSpace →L[ℂ] clusterSpace)
    (hJright : finiteSchur t e ht he * J = 1) (hJleft : J * finiteSchur t e ht he = 1) :
    ‖(inverseFromFinite t e ht he J hJright hJleft).map‖ ≤
      2 + 4 * backgroundAmplitude⁻¹ * ‖J‖ := fullResolvent_norm_le t e ht he J

/-- Any full bounded inverse has the norm of the explicit Feshbach formula. -/
theorem boundedInverse_norm_le
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    ‖R.map‖ ≤ 2 + 4 * backgroundAmplitude⁻¹ * ‖Ring.inverse (finiteSchur t e ht he)‖ := by
  rw [R.unique_map (inverseFromSchur t e ht he (schur_isUnit_of_inverse t e ht he R))]
  exact inverseFromSchur_norm_le t e ht he _

end Maxwell.Continuum.ClusterComplement
