import Maxwell.Continuum.CalibrationFiniteSeedPhysical
import Maxwell.Continuum.CalibrationFixedPowerLower

/-! The literal rational-array iteration is the power of its proved
physical auxiliary approximation. Its normalized limit is the actual
isolated continuum mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber Supercell EffectiveMass NormedSpace MasterConstants

attribute [local irreducible] computedOperator auxiliaryOperator powerOperator
  rawMode seed size precision rootBits Sh realMode

private theorem lift_scaled_identity (M : ℕ) [NeZero M]
    (A S : FieldL2 →L[ℂ] FieldL2) (T : FiberSpace →L[ℂ] FiberSpace) (c : ℂ)
    (hA : A=c • S) (hS : S=physicalLift M T) : A=physicalLift M (c • T) := by
  rw [hA,hS,physicalLift_smul]

theorem computedOperator_lift (L r N : ℕ) (z : ℚ) (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    computedOperator L r N z D =
      physicalLift (size L r N) ((operatorScale L : ℂ) •
        roundedSandwich (size L r N) (scale L r N) z 0 D (by norm_num) (by norm_num; positivity)
          (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)) :=
  lift_scaled_identity _ _ _ _ _ (computedOperator_unfold L r N z D) (auxiliaryOperator_eq L r N z D)

theorem rawMode_eq (L r N : ℕ) (z : ℚ) : rawMode L r N z =
    FourierData.iterate (size L r N) (operatorScale L) (scale L r N) z 0
      (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
      (seed L r N) (iterations N) := by
  unfold rawMode
  rfl

private theorem iterate_transport (M : ℕ) [NeZero M] (v w : FourierData)
    (A B : FieldL2 →L[ℂ] FieldL2) (u : FieldL2) (n : ℕ)
    (hv : v=w) (hA : A=B) (he : embedding M w.value=(B^n) u) :
    embedding M v.value=(A^n) u := by
  rw [hv,hA]
  exact he

theorem rawMode_physical {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    embedding (size L r N) (rawMode L r N z).value =
      (computedOperator L r N z D^iterations N) (embedding (size L r N) (seed L r N).value) := by
  exact iterate_transport _ _ _ _ _ _ _ (rawMode_eq L r N z) (computedOperator_lift L r N z D)
    (finiteIterate_physical (size L r N) (length_ge_one hL)
      (operatorScale L) (scale L r N) z 0 D (by norm_num) (by norm_num; positivity)
      (precision L r N+2) (lengthBits L) (precision L r N) (rootBits L r N)
      (inverseSteps L r N) (cutoffBits L r N) (lengthBits_bound L)
      (selected_inverse_steps_lower L r N) (seed L r N) (iterations N))

private theorem requested_mode_bridge {h z : ℝ} (D : Auxiliary.Calibration h z)
    (hh : h≤1/(2 : ℝ)^1024) (P W n : ℕ) (T : FieldL2 →L[ℂ] FieldL2)
    (w y : FieldL2) (hW : W=powerWorkPrecision P) (hn : n=powerSteps P)
    (hT : ‖T-powerOperator D‖≤(1/2 : ℝ)^W)
    (hw : ‖w-startingVector D.h_pos‖≤(1/2 : ℝ)^W) (hy : y=(T^n) w) :
    ‖normalize y-realMode D hh‖≤(1/2 : ℝ)^P := by
  subst W n
  rw [hy]
  exact (fixed_power_requested_error D hh P T w hT hw).2

theorem rawMode_normalized_error {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    ‖normalize (embedding (size L r N) (rawMode L r N z).value)-
      realMode D (inverse_length_le_1024 hL)‖ ≤ (1/2 : ℝ)^targetPrecision N :=
  requested_mode_bridge D (inverse_length_le_1024 hL) (targetPrecision N) (workPrecision N)
    (iterations N) (computedOperator L r N z D) (embedding (size L r N) (seed L r N).value)
    (embedding (size L r N) (rawMode L r N z).value) rfl rfl
    (computedOperator_error hL r N z D) (seed_physical_error hL r N) (rawMode_physical hL r N z D)

private theorem norm_lower_transport (M : ℕ) [NeZero M] (v : FourierData)
    (w : FieldL2) {δ : ℝ} (hv : embedding M v.value=w) (hw : δ≤‖w‖) : δ≤‖v.value‖ := by
  rw [← embedding_norm M,hv]
  exact hw

theorem rawMode_norm_lower {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) :
    (1/2 : ℝ)^(49+38*iterations N) ≤ ‖(rawMode L r N z).value‖ := by
  have hl := fixed_power_norm_lower D (inverse_length_le_1024 hL) (targetPrecision N)
    (iterations N) (Nat.clog 2 (iterations N+1)) (computedOperator L r N z D)
    (embedding (size L r N) (seed L r N).value)
    (computedOperator_error hL r N z D) (seed_physical_error hL r N)
  exact norm_lower_transport _ _ _ (rawMode_physical hL r N z D) hl

#print axioms rawMode_physical
#print axioms rawMode_normalized_error
#print axioms rawMode_norm_lower
end Maxwell.Continuum.Calibration.FiniteAlgorithm
