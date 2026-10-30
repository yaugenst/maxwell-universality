import Maxwell.Continuum.CalibrationSchur
import Maxwell.Continuum.FiberEnergy

/-! Real-energy symmetry and the exact resolvent identity for the
literal 24-dimensional calibration Schur complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped InnerProductSpace

theorem central_inner (u v : FiberSpace) :
    inner ℂ (centralAliasProjection u) v = inner ℂ u (centralAliasProjection v) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    centralAliasProjection_projection.isSelfAdjoint) u v

theorem noncentral_inner (u v : FiberSpace) :
    inner ℂ (noncentralAliasProjection u) v = inner ℂ u (noncentralAliasProjection v) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    centralAliasProjection_projection.one_sub.isSelfAdjoint) u v

theorem calibrationComplementInverse_noncentral_input (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    calibrationComplementInverse t e ht he (noncentralAliasProjection u) =
      calibrationComplementInverse t e ht he u := by
  change (calibrationMaterialInverse t e ht he).map
    (noncentralAliasProjection (noncentralAliasProjection u)) = _
  rw [noncentralAliasProjection_idempotent]
  rfl

theorem calibrationComplementInverse_resolvent (t : Momentum) (e f : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (hf : ‖f‖ ≤ 8)
    (u : FiberSpace) :
    calibrationComplementInverse t f ht hf u-calibrationComplementInverse t e ht he u =
      (totalEnergy f-totalEnergy e) •
        calibrationComplementInverse t f ht hf (calibrationComplementInverse t e ht he u) := by
  let x : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain :=
    ⟨calibrationComplementInverse t e ht he u, calibrationComplementInverse_mem_domain t e ht he u⟩
  have hx : (x.val, materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude x) ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph :=
    LinearPMap.mem_graph _ x
  have hs := material_graph_energy_shift (scaledMomentum t) (totalEnergy e) (totalEnergy f)
    backgroundAmplitude x.val _ hx
  rw [LinearPMap.mem_graph_iff] at hs
  obtain ⟨y, hy, hAy⟩ := hs
  dsimp only at hy hAy
  have hQy : noncentralAliasProjection y.val = y.val := by
    rw [hy]
    exact noncentral_calibrationComplementInverse t e ht he u
  have hi := calibrationComplementInverse_map_apply t f ht hf y hQy
  rw [hAy, map_add, map_smul, hy] at hi
  have hv : calibrationComplementInverse t f ht hf
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude x) =
        calibrationComplementInverse t f ht hf u := by
    rw [← calibrationComplementInverse_noncentral_input t f ht hf,
      calibrationComplementInverse_apply, calibrationComplementInverse_noncentral_input]
  rw [hv] at hi
  change calibrationComplementInverse t f ht hf u+
      (totalEnergy e-totalEnergy f) • calibrationComplementInverse t f ht hf
        (calibrationComplementInverse t e ht he u) = calibrationComplementInverse t e ht he u at hi
  rw [← neg_sub (totalEnergy f) (totalEnergy e), neg_smul] at hi
  change calibrationComplementInverse t f ht hf u-
      (totalEnergy f-totalEnergy e) • calibrationComplementInverse t f ht hf
        (calibrationComplementInverse t e ht he u) = calibrationComplementInverse t e ht he u at hi
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp hi))

theorem edgeParameterBound : ∀ j : Fin 3, ‖(0 : Momentum) j‖ ≤ ((2 : ℝ)^12)⁻¹ := by
  intro j
  simp only [Pi.zero_apply, norm_zero]
  positivity

theorem edgeEnergyBound {e : ℝ} (he : |e| ≤ 8) : ‖(e : ℂ)‖ ≤ 8 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using he

theorem edgeMaterial_formalAdjoint (e : ℝ) :
    (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude).IsFormalAdjoint
      (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude) := by
  have h : IsSelfAdjoint
      (materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude) := by
    have hq : scaledMomentum (0 : Momentum) = realMomentum (0 : Fin 3 → ℝ) := by
      funext j
      simp only [scaledMomentum, Pi.zero_apply, mul_zero, realMomentum, Complex.ofReal_zero]
    have hE : totalEnergy (e : ℂ) = ((3*Real.pi^2/4+backgroundAmplitude*e : ℝ) : ℂ) := by
      simp only [totalEnergy, Complex.ofReal_add, Complex.ofReal_mul]
    rw [hq, hE]
    exact real_materialFiber_selfAdjoint (0 : Fin 3 → ℝ)
      (3*Real.pi^2/4+backgroundAmplitude*e) backgroundAmplitude
  simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
    LinearPMap.adjoint_isFormalAdjoint h.dense_domain

theorem edgeComplement_isSymmetric (e : ℝ) (he : |e| ≤ 8) :
    (calibrationComplementInverse 0 e edgeParameterBound (edgeEnergyBound he)).IsSymmetric := by
  let R := calibrationComplementInverse 0 (e : ℂ) edgeParameterBound (edgeEnergyBound he)
  let A := materialFiber (scaledMomentum 0) (totalEnergy (e : ℂ)) backgroundAmplitude
  intro u v
  let x : A.domain := ⟨R u, calibrationComplementInverse_mem_domain _ _ _ _ u⟩
  let y : A.domain := ⟨R v, calibrationComplementInverse_mem_domain _ _ _ _ v⟩
  have hxu : noncentralAliasProjection x.val = x.val := noncentral_calibrationComplementInverse _ _ _ _ u
  have hyv : noncentralAliasProjection y.val = y.val := noncentral_calibrationComplementInverse _ _ _ _ v
  have hAx : noncentralAliasProjection (A x) = noncentralAliasProjection u :=
    calibrationComplementInverse_apply _ _ _ _ u
  have hAy : noncentralAliasProjection (A y) = noncentralAliasProjection v :=
    calibrationComplementInverse_apply _ _ _ _ v
  change inner ℂ x.val v = inner ℂ u y.val
  calc
    _ = inner ℂ x.val (noncentralAliasProjection v) := by rw [← noncentral_inner, hxu]
    _ = inner ℂ x.val (A y) := by rw [← hAy, ← noncentral_inner, hxu]
    _ = inner ℂ (A x) y.val := ((edgeMaterial_formalAdjoint e) x y).symm
    _ = inner ℂ (noncentralAliasProjection u) y.val := by rw [← hAx, noncentral_inner, hyv]
    _ = inner ℂ u y.val := by rw [noncentral_inner, hyv]

theorem calibrationSchur_inner_lift (t : Momentum) (e f : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (hf : ‖f‖ ≤ 8)
    (u v : FiberSpace) :
    inner ℂ (calibrationSchur t e ht he u) (calibrationLift t f ht hf v) =
      inner ℂ (calibrationSchur t e ht he u) v := by
  calc
    _ = inner ℂ (calibrationSchur t e ht he u)
        (centralAliasProjection (calibrationLift t f ht hf v)) := by
      rw [← central_inner, calibrationSchur_central]
    _ = _ := by rw [calibrationLift_central, ← central_inner, calibrationSchur_central]

theorem calibrationLift_inner_schur (t : Momentum) (e f : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (hf : ‖f‖ ≤ 8)
    (u v : FiberSpace) :
    inner ℂ (calibrationLift t e ht he u) (calibrationSchur t f ht hf v) =
      inner ℂ u (calibrationSchur t f ht hf v) := by
  rw [← inner_conj_symm, calibrationSchur_inner_lift, inner_conj_symm]

theorem edgeSchur_isSymmetric (e : ℝ) (he : |e| ≤ 8) :
    (calibrationFiniteSchur 0 e edgeParameterBound (edgeEnergyBound he)).IsSymmetric := by
  intro u v
  have hs := edgeMaterial_formalAdjoint e
    ⟨calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) u.val,
      calibrationLift_mem_domain _ _ _ _ u.val⟩
    ⟨calibrationLift 0 e edgeParameterBound (edgeEnergyBound he) v.val,
      calibrationLift_mem_domain _ _ _ _ v.val⟩
  rw [calibrationLift_residual, calibrationLift_residual, calibrationSchur_inner_lift,
    calibrationLift_inner_schur] at hs
  exact hs

#print axioms calibrationComplementInverse_resolvent
#print axioms edgeComplement_isSymmetric
#print axioms edgeSchur_isSymmetric

end Maxwell.Continuum.Calibration
