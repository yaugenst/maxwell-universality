import Maxwell.Continuum.AuxiliaryFiberEnergy
import Maxwell.Continuum.FreeFiberResolventIdentity

/-! The actual maximal-domain fiber inverse underlying the cutoff
resolvent, with the paper's inverse and detuning bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Metric

attribute [local irreducible] fullResolventExtension scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

def fiberResolvent (z σ : ℝ) (q : Corner.Vec) : FiberMap :=
  fullResolventExtension (fiberParameter q, sampledScaledEnergy z σ)

def transportedInverse {A B : FiberSpace →ₗ.[ℂ] FiberSpace} (hAB : A = B)
    (R : SelfAdjointResolvent.BoundedInverse A) : SelfAdjointResolvent.BoundedInverse B :=
  hAB ▸ R

theorem transportedInverse_map {A B : FiberSpace →ₗ.[ℂ] FiberSpace} (hAB : A = B)
    (R : SelfAdjointResolvent.BoundedInverse A) : (transportedInverse hAB R).map = R.map := by
  subst B
  rfl

theorem sampledFiber_eq (z σ : ℝ) (q : Corner.Vec) :
    materialFiber (scaledMomentum (fiberParameter q))
      (totalEnergy (sampledScaledEnergy z σ)) backgroundAmplitude =
      materialFiber (realMomentum q) (sampledEnergy z σ) backgroundAmplitude := by
  rw [fiberParameter, scaledMomentum_unscale, sampledScaledEnergy, totalEnergy_scaledEnergy]

theorem sampledScaledEnergy_wide {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    ‖sampledScaledEnergy z σ - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
  apply energy_near_band_in_wide (fiberParameter_chart q hq)
  have he := sampledScaledEnergy_mem D hσ0 hσ q hq
  rw [mem_closedBall, dist_eq_norm] at he
  linarith

/-- The inverse is on the complete actual fiber domain, including every
longitudinal alias. -/
def fiberInverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    SelfAdjointResolvent.BoundedInverse
      (materialFiber (realMomentum q) (sampledEnergy z σ) backgroundAmplitude) :=
  transportedInverse (sampledFiber_eq z σ q)
    (inverseAwayFromBand (fiberParameter_chart q hq)
      (sampledScaledEnergy_wide D hσ0 hσ q hq)
      (sampledScaledEnergy_ne_band D hσ0 hσ q hq))

theorem fiberResolvent_eq_inverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    fiberResolvent z σ q = (fiberInverse D hσ0 hσ q hq).map := by
  rw [fiberInverse, transportedInverse_map]
  exact fullResolventExtension_eq_inverseAwayFromBand (fiberParameter_chart q hq)
    (sampledScaledEnergy_wide D hσ0 hσ q hq)
    (sampledScaledEnergy_ne_band D hσ0 hσ q hq)

theorem separated_bound_le_inverse_square {h z : ℝ} (D : Calibration h z) :
    (2 : ℝ)^112 ≤ 2 * (h ^ 2)⁻¹ := by
  have hh : h ^ 2 ≤ backgroundAmplitude ^ 2 := by
    nlinarith [D.h_pos, D.h_le, backgroundAmplitude_pos]
  have hnum : (2 : ℝ)^112 * backgroundAmplitude ^ 2 ≤ 2 := by
    norm_num [backgroundAmplitude]
  apply (le_mul_inv_iff₀ (sq_pos_of_pos D.h_pos)).mpr
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hnum

theorem fiberResolvent_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    ‖fiberResolvent z σ q‖ ≤ 4 * (h ^ 2)⁻¹ := by
  have hn := fullResolventExtension_norm_le_real_band
    (fun j => q j / backgroundAmplitude)
    (e := sampledScaledEnergy z σ)
    (by rw [← fiberParameter_real]; exact fiberParameter_chart q hq)
    (by rw [← fiberParameter_real]; exact sampledScaledEnergy_mem D hσ0 hσ q hq)
    (by rw [← fiberParameter_real]; exact sampledScaledEnergy_ne_band D hσ0 hσ q hq)
  rw [← fiberParameter_real, sampledScaledEnergy, totalEnergy_scaledEnergy] at hn
  have hd := (sampledEnergy_distance_bounds D hσ0 hσ q hq).1
  have hi : ‖sampledEnergy z σ - physicalBand (fiberParameter q)‖⁻¹ ≤
      2 * (h ^ 2)⁻¹ := by
    have hpos : 0 < h ^ 2 / 2 := div_pos (sq_pos_of_pos D.h_pos) (by norm_num)
    calc
      _ ≤ (h ^ 2 / 2)⁻¹ := inv_anti₀ hpos hd
      _ = _ := by ring
  change ‖fiberResolvent z σ q‖ ≤ _ at hn
  linarith [separated_bound_le_inverse_square D]

theorem fiberResolvent_selfAdjoint {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    IsSelfAdjoint (fiberResolvent z σ q) := by
  rw [fiberResolvent_eq_inverse D hσ0 hσ q hq]
  exact (fiberInverse D hσ0 hσ q hq).map_selfAdjoint
    (real_materialFiber_selfAdjoint q (z + σ + 7) backgroundAmplitude)

theorem fiberResolvent_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    fiberResolvent z σ q - fiberResolvent z 0 q =
      (σ : ℂ) • (fiberResolvent z σ q * fiberResolvent z 0 q) := by
  have h0 : (0 : ℝ) ≤ h ^ 4 / 64 := by positivity
  have hi := material_resolvent_identity (realMomentum q)
    (sampledEnergy z σ) (sampledEnergy z 0) backgroundAmplitude
    (fiberInverse D hσ0 hσ q hq) (fiberInverse D le_rfl h0 q hq)
  rw [← fiberResolvent_eq_inverse D hσ0 hσ q hq,
    ← fiberResolvent_eq_inverse D le_rfl h0 q hq] at hi
  have hE : sampledEnergy z σ - sampledEnergy z 0 = (σ : ℂ) := by
    unfold sampledEnergy
    push_cast
    ring
  rwa [hE] at hi

theorem fiberResolvent_difference_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    ‖fiberResolvent z σ q - fiberResolvent z 0 q‖ ≤ 16 * σ * (h ^ 4)⁻¹ := by
  rw [fiberResolvent_identity D hσ0 hσ q hq, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hσ0]
  have h0 : (0 : ℝ) ≤ h ^ 4 / 64 := by positivity
  calc
    _ ≤ σ * (‖fiberResolvent z σ q‖ * ‖fiberResolvent z 0 q‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) hσ0
    _ ≤ σ * ((4 * (h ^ 2)⁻¹) * (4 * (h ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (fiberResolvent_norm_le D hσ0 hσ q hq)
        (fiberResolvent_norm_le D le_rfl h0 q hq) (norm_nonneg _) (by positivity)) hσ0
    _ = _ := by ring

end Maxwell.Continuum.Auxiliary
