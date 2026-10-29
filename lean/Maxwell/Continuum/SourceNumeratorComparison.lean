import Maxwell.Continuum.SourceNumerator

/-! Reality and stability of the literal source factors. These estimates
apply to both signs of imaginary physical momentum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand FiberNormalization Set Metric

attribute [local instance] Measure.Subtype.measureSpace

attribute [local irreducible] Auxiliary.resolvent PeriodicPerturbation.perturbation
  PeriodicPerturbation.finiteK CornerBridge.topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector physicalFiberVector

theorem sourceValue_sub_ae (h : ℝ) (u v : FieldL2) :
    sourceValue h (u-v) =ᵐ[volume] fun x => sourceValue h u x - sourceValue h v x := by
  have he : sourceMode h (u-v) = sourceMode h u - sourceMode h v := map_sub (Qh h) u v
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_sub (sourceMode h u j) (sourceMode h v j))]
    with x hx
  apply PiLp.ext
  intro j
  change sourceMode h (u-v) j x = sourceMode h u j x - sourceMode h v j x
  rw [he]
  exact hx j

theorem sourceFactor_sub {h : ℝ} (hh : 0 < h) (u v : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    sourceFactor h (u-v) q = sourceFactor h u q - sourceFactor h v q := by
  rw [sourceFactor, sourceFactor, sourceFactor, ← mul_sub,
    ← integral_sub (sourceIntegrand_integrable hh u hq) (sourceIntegrand_integrable hh v hq)]
  congr 1
  apply integral_congr_ae
  filter_upwards [sourceValue_sub_ae h u v] with x hx
  simp only [sourceIntegrand, hx, map_sub, mul_sub]

theorem sourceFactor_scaled_norm_small {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {q : Momentum} (hq : q ∈ physicalChart) (hi : ‖sourceImaginary q‖ ≤ h) :
    sourceScale h * ‖sourceFactor h u q‖ ≤ 384 * ‖u‖ := by
  have he : Real.exp (‖sourceImaginary q‖ / h) ≤ 4 :=
    (Real.exp_le_exp.mpr ((div_le_one hh).mpr hi)).trans
      (Real.exp_one_lt_three.le.trans (by norm_num))
  exact (sourceFactor_scaled_norm_le hh u hq).trans (by
    nlinarith [norm_nonneg u])

theorem sourceFactor_scaled_sub_le {h : ℝ} (hh : 0 < h) (u v : FieldL2)
    {q : Momentum} (hq : q ∈ physicalChart) (hi : ‖sourceImaginary q‖ ≤ h) :
    sourceScale h * ‖sourceFactor h u q - sourceFactor h v q‖ ≤ 512 * ‖u-v‖ := by
  rw [← sourceFactor_sub hh u v hq]
  exact (sourceFactor_scaled_norm_small hh (u-v) hq hi).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

theorem sourceFactor_real {h : ℝ} {u : FieldL2} (hu : fieldConjugation u = u)
    {q : Momentum} (hq : q ∈ physicalChart) (hi : star q = -q) :
    star (sourceFactor h u q) = sourceFactor h u q := by
  have hre : ∀ᵐ x ∂(volume : Measure Space), star (sourceIntegrand h u q x) =
      sourceIntegrand h u q x := by
    filter_upwards [sourceValue_real (h := h) hu] with x hx
    rw [sourceIntegrand, star_mul', sourcePhase_star hi]
    congr 1
    rw [bilinear_apply, sourceCell_real hq hi]
    rw [← polarization_inner_star, sourceCell_real hq hi, hx]
  rw [sourceFactor, star_mul', Complex.star_def, Complex.conj_ofReal]
  congr 1
  rw [← integral_conj]
  exact integral_congr_ae hre

theorem sourcePairing_norm_le (h : ℝ) (u : FieldL2) :
    ‖sourcePairing h u‖ ≤ ∫ x : SourceBall h, ‖sourceValue h u x.val‖ := by
  exact (sourcePairingLinear h u).mkContinuous_norm_le
    (integral_nonneg (fun _ => norm_nonneg _)) _

theorem sourcePairing_scaled_norm_le {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    sourceScale h * ‖sourcePairing h u‖ ≤ 3 * ‖u‖ := by
  apply (mul_le_mul_of_nonneg_left (sourcePairing_norm_le h u) (sourceScale_pos hh).le).trans
  rw [integral_subtype (s := SourceBall h) measurableSet_closedBall
    (fun x : Space => ‖sourceValue h u x‖)]
  have he : ∫ x in SourceBall h, ‖sourceValue h u x‖ = ∫ x, ‖sourceValue h u x‖ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [sourceValue_supported hh u] with x hx hn
    simp only [SourceBall, mem_closedBall, dist_zero_right, not_le] at hn
    rw [hx hn.le, norm_zero]
  rw [he]
  exact sourceValue_scaled_integral_norm_le hh u

theorem sourceCell_norm_le (h : ℝ) : ‖sourceCell h‖ ≤ 1 :=
  (sourceCellLinear h).mkContinuous_norm_le zero_le_one _

theorem sourcePhase_opNorm_le {h : ℝ} (hh : 0 < h) (q : Momentum) :
    ‖sourcePhase h q‖ ≤ Real.exp (‖sourceImaginary q‖ / h) := by
  apply (ContinuousMap.norm_le _ (Real.exp_nonneg _)).mpr
  intro x
  rw [sourcePhase_apply]
  apply sourcePhase_norm_on_support hh
  simpa only [SourceBall, mem_closedBall, dist_zero_right] using x.property

theorem source_zero_mem_physicalChart : (0 : Momentum) ∈ physicalChart := by
  intro j
  simpa only [Pi.zero_apply, norm_zero] using analyticRadius_pos

def sourceFrozenFactor (h : ℝ) (u : FieldL2) (q : Momentum) : ℂ :=
  (fourierNormalization : ℂ) *
    ∫ x, spatialPhase q x * bilinear (cellEigenfunction 0 x) (sourceValue h u x)

theorem sourceFrozenFactor_integral {h : ℝ} (_hh : 0 < h) (u : FieldL2) (q : Momentum) :
    sourceFrozenFactor h u q = (fourierNormalization : ℂ) *
      ∫ x, spatialPhase q x * bilinear (cellEigenfunction 0 x) (sourceValue h u x) := rfl

theorem sourceFrozenFactor_eq_pairing {h : ℝ} (hh : 0 < h) (u : FieldL2) (q : Momentum) :
    sourceFrozenFactor h u q = (fourierNormalization : ℂ) * sourcePairing h u
      (sourcePhase h q • sourceCell h (physicalFiberL1 0)) := by
  rw [sourceFrozenFactor, sourcePairing_apply]
  congr 1
  have heq : (fun x : SourceBall h =>
      bilinear ((sourcePhase h q • sourceCell h (physicalFiberL1 0)) x) (sourceValue h u x.val)) =
      fun x : SourceBall h => spatialPhase q x.val *
        bilinear (cellEigenfunction 0 x.val) (sourceValue h u x.val) := by
    funext x
    rw [ContinuousMap.smul_apply', sourcePhase_apply,
      sourceCell_physical h source_zero_mem_physicalChart, map_smul, smul_apply]
    simp only [unscale, smul_zero, smul_eq_mul]
  rw [heq, integral_subtype (s := SourceBall h) measurableSet_closedBall
    (fun x : Space => spatialPhase q x * bilinear (cellEigenfunction 0 x) (sourceValue h u x))]
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [sourceValue_supported hh u] with x hx hn
  simp only [SourceBall, mem_closedBall, dist_zero_right, not_le] at hn
  simp only [hx hn.le, map_zero, mul_zero]

theorem sourceFactor_frozen_sub_le {h : ℝ} (hh : 0 < h) (u : FieldL2)
    {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) (hi : ‖sourceImaginary q‖ ≤ h) :
    sourceScale h * ‖sourceFactor h u q - sourceFrozenFactor h u q‖ ≤
      12 * ((128 / analyticRadius) * ‖q‖) * ‖u‖ := by
  have hchart : q ∈ physicalChart := by
    intro j
    exact (norm_le_pi_norm q j).trans_lt (hq.trans_lt (by linarith [analyticRadius_pos]))
  have hp : ‖sourcePhase h q‖ ≤ 4 := (sourcePhase_opNorm_le hh q).trans
    ((Real.exp_le_exp.mpr ((div_le_one hh).mpr hi)).trans
      (Real.exp_one_lt_three.le.trans (by norm_num)))
  have hc : ‖sourceCell h (physicalFiberL1 q - physicalFiberL1 0)‖ ≤
      (128 / analyticRadius) * ‖q‖ :=
    ((sourceCell h).le_of_opNorm_le (sourceCell_norm_le h) _).trans
      (by simpa only [one_mul] using physicalFiberL1_sub_zero hq)
  have heq : sourceFactor h u q - sourceFrozenFactor h u q =
      (fourierNormalization : ℂ) * sourcePairing h u
        (sourcePhase h q • sourceCell h (physicalFiberL1 q - physicalFiberL1 0)) := by
    rw [sourceFactor_eq_pairing hh u hchart, sourceFrozenFactor_eq_pairing hh, sourceCellWave]
    have hs := smul_sub (sourcePhase h q) (sourceCell h (physicalFiberL1 q))
      (sourceCell h (physicalFiberL1 0))
    rw [map_sub, hs, map_sub, mul_sub]
  rw [heq, norm_mul]
  have hb : ‖(fourierNormalization : ℂ)‖ * ‖sourcePairing h u
      (sourcePhase h q • sourceCell h (physicalFiberL1 q - physicalFiberL1 0))‖ ≤
      ‖sourcePairing h u‖ * (4 * ((128 / analyticRadius) * ‖q‖)) := by
    apply (mul_le_mul_of_nonneg_right fourierNormalization_norm_le (norm_nonneg _)).trans
    rw [one_mul]
    apply ((sourcePairing h u).le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_smul_le (sourcePhase h q)
      (sourceCell h (physicalFiberL1 q - physicalFiberL1 0))).trans
      (mul_le_mul hp hc (norm_nonneg _) (by norm_num))
  calc
    _ ≤ sourceScale h * (‖sourcePairing h u‖ * (4 * ((128 / analyticRadius) * ‖q‖))) :=
      mul_le_mul_of_nonneg_left hb (sourceScale_pos hh).le
    _ = (sourceScale h * ‖sourcePairing h u‖) * (4 * ((128 / analyticRadius) * ‖q‖)) :=
      (mul_assoc _ _ _).symm
    _ ≤ (3 * ‖u‖) * (4 * ((128 / analyticRadius) * ‖q‖)) :=
      mul_le_mul_of_nonneg_right (sourcePairing_scaled_norm_le hh u)
        (mul_nonneg (by norm_num)
          (mul_nonneg (div_nonneg (by norm_num) analyticRadius_pos.le) (norm_nonneg q)))
    _ = _ := by ring

#print axioms sourceFactor_scaled_sub_le
#print axioms sourceFactor_real
#print axioms sourceFactor_frozen_sub_le

end Maxwell.Continuum.EffectiveMass
