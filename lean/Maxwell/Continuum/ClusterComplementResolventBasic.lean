import Maxwell.Continuum.ClusterComplementKernel

/-!
# The literal continuum Feshbach inverse formula

These bounded maps use the actual infinite complementary inverse and the
literal sixteen-dimensional Schur operator. Every output is proved to
belong to the original momentum-dependent maximal domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

/-- The actual orthogonal projection with its range as codomain. -/
def clusterProjectionToSpace : FiberSpace →L[ℂ] clusterSpace :=
  clusterProjection.codRestrict clusterSpace
    (fun u => (mem_clusterSpace_iff _).mpr (clusterProjection_idempotent u))

@[simp] theorem clusterProjectionToSpace_apply (u : FiberSpace) :
    (clusterProjectionToSpace u).val = clusterProjection u := rfl

theorem clusterProjectionToSpace_norm_le : ‖clusterProjectionToSpace‖ ≤ 1 := by
  apply clusterProjectionToSpace.opNorm_le_bound (by norm_num)
  intro u
  exact (clusterProjection.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right clusterProjection_norm_le (norm_nonneg u))

theorem clusterProjectionToSpace_coe (u : clusterSpace) : clusterProjectionToSpace u.val = u := by
  apply Subtype.ext
  exact (mem_clusterSpace_iff _).mp u.property

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)

theorem schurLift_norm_le : ‖schurLift t e ht he‖ ≤ 2 := by
  have h := (norm_sub_le clusterProjection
    (complementInverse t e ht he * rightCoupling t (totalEnergy e) ht)).trans
      (add_le_add clusterProjection_norm_le ((norm_mul_le _ _).trans
        (mul_le_mul (complementInverse_norm_le t e ht he)
          (rightCoupling_norm_le t (totalEnergy e) ht) (norm_nonneg _) (by norm_num))))
  change ‖schurLift t e ht he‖ ≤ _ at h
  have hρ := backgroundAmplitude_le
  nlinarith

/-- The complete residual of the actual infinite complementary inverse. -/
theorem complementInverse_full_residual (f : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨complementInverse t e ht he f,complementInverse_mem_domain t e ht he f⟩ =
      complementProjection f + leftCoupling t (totalEnergy e) ht (complementInverse t e ht he f) := by
  have hp := leftCoupling_on_complement t (totalEnergy e) ht
    ⟨complementInverse t e ht he f,complementInverse_mem_domain t e ht he f⟩
    (complementProjection_complementInverse t e ht he f)
  have hq := complementInverse_apply t e ht he f
  change _ - clusterProjection _ = complementProjection f at hq
  rw [← hp] at hq
  exact eq_add_of_sub_eq hq

theorem clusterProjection_left_inverse (f : FiberSpace) :
    clusterProjection (leftCoupling t (totalEnergy e) ht (complementInverse t e ht he f)) =
      leftCoupling t (totalEnergy e) ht (complementInverse t e ht he f) := by
  have hp := leftCoupling_on_complement t (totalEnergy e) ht
    ⟨complementInverse t e ht he f,complementInverse_mem_domain t e ht he f⟩
    (complementProjection_complementInverse t e ht he f)
  rw [hp,clusterProjection_idempotent]

/-- Right-hand side after elimination of the complementary variables. -/
def adjustedSource : FiberSpace →L[ℂ] clusterSpace :=
  clusterProjectionToSpace.comp
    (1 - leftCoupling t (totalEnergy e) ht * complementInverse t e ht he)

theorem adjustedSource_apply (f : FiberSpace) :
    (adjustedSource t e ht he f).val = clusterProjection f -
      leftCoupling t (totalEnergy e) ht (complementInverse t e ht he f) := by
  change clusterProjection (f - leftCoupling t (totalEnergy e) ht (complementInverse t e ht he f)) = _
  rw [map_sub,clusterProjection_left_inverse]

theorem adjustedSource_norm_le : ‖adjustedSource t e ht he‖ ≤ 2 := by
  have hc : ‖leftCoupling t (totalEnergy e) ht * complementInverse t e ht he‖ ≤
      16 * backgroundAmplitude :=
    (norm_mul_le _ _).trans ((mul_le_mul (leftCoupling_norm_le t (totalEnergy e) ht)
      (complementInverse_norm_le t e ht he) (norm_nonneg _)
      (mul_nonneg (by norm_num) backgroundAmplitude_pos.le)).trans_eq (by ring))
  have hs : ‖(1 : FiberSpace →L[ℂ] FiberSpace) -
      leftCoupling t (totalEnergy e) ht * complementInverse t e ht he‖ ≤ 2 := by
    have h := (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hc)
    change ‖(1 : FiberSpace →L[ℂ] FiberSpace) -
      leftCoupling t (totalEnergy e) ht * complementInverse t e ht he‖ ≤
        1 + 16 * backgroundAmplitude at h
    have hρ := backgroundAmplitude_le
    linarith
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul clusterProjectionToSpace_norm_le hs (norm_nonneg _) (by norm_num)).trans_eq (by ring))

/-- Feshbach formula with an arbitrary candidate finite inverse. -/
def fullResolvent (J : clusterSpace →L[ℂ] clusterSpace) : FiberSpace →L[ℂ] FiberSpace :=
  complementInverse t e ht he + (backgroundAmplitude : ℂ)⁻¹ •
    ((schurLift t e ht he).comp (clusterSpace.subtypeL.comp (J.comp (adjustedSource t e ht he))))

theorem fullResolvent_apply (J : clusterSpace →L[ℂ] clusterSpace) (f : FiberSpace) :
    fullResolvent t e ht he J f = complementInverse t e ht he f + (backgroundAmplitude : ℂ)⁻¹ •
      schurLift t e ht he (J (adjustedSource t e ht he f)).val := rfl

theorem fullResolvent_mem_domain (J : clusterSpace →L[ℂ] clusterSpace) (f : FiberSpace) :
    fullResolvent t e ht he J f ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain := by
  rw [fullResolvent_apply]
  exact Submodule.add_mem _ (complementInverse_mem_domain t e ht he f)
    (Submodule.smul_mem _ _ (schurLift_mem_domain t e ht he _))

theorem fullResolvent_norm_le (J : clusterSpace →L[ℂ] clusterSpace) :
    ‖fullResolvent t e ht he J‖ ≤ 2 + 4 * backgroundAmplitude⁻¹ * ‖J‖ := by
  have hc : ‖(schurLift t e ht he).comp
      (clusterSpace.subtypeL.comp (J.comp (adjustedSource t e ht he)))‖ ≤ 4 * ‖J‖ := by
    calc
      _ ≤ ‖schurLift t e ht he‖ * (‖clusterSpace.subtypeL‖ * (‖J‖ * ‖adjustedSource t e ht he‖)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
              (norm_nonneg _))
      _ ≤ 2 * (1 * (‖J‖ * 2)) := by
        gcongr
        · exact schurLift_norm_le t e ht he
        · exact clusterSpace.norm_subtypeL_le
        · exact adjustedSource_norm_le t e ht he
      _ = _ := by ring
  have h := norm_add_le (complementInverse t e ht he)
    ((backgroundAmplitude : ℂ)⁻¹ • ((schurLift t e ht he).comp
      (clusterSpace.subtypeL.comp (J.comp (adjustedSource t e ht he)))))
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos backgroundAmplitude_pos] at h
  change ‖fullResolvent t e ht he J‖ ≤ _ at h
  exact h.trans ((add_le_add (complementInverse_norm_le t e ht he)
    (mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr backgroundAmplitude_pos.le))).trans_eq (by ring))

end Maxwell.Continuum.ClusterComplement
