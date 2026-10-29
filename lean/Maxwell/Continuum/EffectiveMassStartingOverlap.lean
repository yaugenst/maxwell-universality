import Maxwell.Continuum.EffectiveMassStartingEnvelope
import Maxwell.Continuum.InnerOverlapStability

/-! The actual normalized calibration starting vector has quantitatively
positive overlap with every sufficiently close physical effective-mass mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber

attribute [local irreducible] startingEnvelope rootEnvelope referencePhysicalMode

theorem startingEnvelope_reference_overlap {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) :
    1 / (2 : ℝ)^34 ≤ (inner ℂ (startingEnvelope hh) (referencePhysicalMode hh)).re := by
  have hdiff : ‖rootEnvelope hh - startingEnvelope hh‖ ≤
      3 * (2 : ℝ)^16 * backgroundAmplitude := by
    rw [norm_sub_rev]
    exact startingEnvelope_root_error hh
  have hn : ‖referencePhysicalMode hh‖ ≤ 32 := by
    rw [referencePhysicalMode]
    change ‖envelopeOperator hh Well.topVector‖ ≤ 32
    calc
      _ ≤ 32 * ‖Well.topVector‖ :=
        (envelopeOperator hh).le_of_opNorm_le (envelopeOperator_norm hh) Well.topVector
      _ = _ := by rw [Well.topVector_norm, mul_one]
  have he := mul_le_mul hdiff hn (norm_nonneg _)
    (mul_nonneg (by positivity : 0 ≤ 3 * (2 : ℝ)^16) backgroundAmplitude_pos.le)
  have hl := sub_le_sub (rootEnvelope_mode_overlap hh hsmall) he
  have hfinal := hl.trans (inner_re_lower_left (rootEnvelope hh) (startingEnvelope hh)
    (referencePhysicalMode hh))
  exact le_trans (by norm_num [backgroundAmplitude]) hfinal

theorem startingEnvelope_ne_zero {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) : startingEnvelope hh ≠ 0 := by
  intro hz
  have he := startingEnvelope_reference_overlap hh hsmall
  rw [hz, inner_zero_left] at he
  norm_num at he

def startingVector {h : ℝ} (hh : 0 < h) : FieldL2 := NormedSpace.normalize (startingEnvelope hh)

theorem startingVector_norm {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) : ‖startingVector hh‖ = 1 :=
  NormedSpace.norm_normalize (startingEnvelope_ne_zero hh hsmall)

theorem startingVector_overlap_of_spatial_error {h : ℝ} (hh : 0 < h)
    (hsmall : h ≤ 1 / (2 : ℝ)^1024) (u : FieldL2)
    (hu : ‖u - referencePhysicalMode hh‖ ≤ 1 / (2 : ℝ)^48) :
    1 / (2 : ℝ)^48 ≤ (inner ℂ (startingVector hh) u).re := by
  have hn : ‖startingEnvelope hh‖ ≤ 128 := (startingEnvelope_norm_le hh).trans (by norm_num)
  have hd : ‖referencePhysicalMode hh - u‖ ≤ 1 / (2 : ℝ)^48 := by
    rwa [norm_sub_rev]
  have he := mul_le_mul hn hd (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 128)
  have hl := (sub_le_sub (startingEnvelope_reference_overlap hh hsmall) he).trans
    (inner_re_lower_right (startingEnvelope hh) (referencePhysicalMode hh) u)
  have ho : 1 / (2 : ℝ)^35 ≤ (inner ℂ (startingEnvelope hh) u).re :=
    le_trans (by norm_num) hl
  have hfinal := normalized_overlap_lower (by positivity : (0 : ℝ) < 1 / 2^35)
    (by norm_num : (0 : ℝ) < 128) hn ho
  exact le_trans (by norm_num) hfinal

end Maxwell.Continuum.EffectiveMass
