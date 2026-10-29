import Maxwell.Continuum.EffectiveMassScalingPacket
import Maxwell.Continuum.EffectiveMassMultiplierMeasurable
import Maxwell.Continuum.VectorMultiplier

/-! The literal broad-well packet operator B_h=Q_h U_h s_h and its
positive Gram operator on angular-momentum L². -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary
open scoped InnerProduct

theorem cutoffBandMultiplier_indicator {h z : ℝ} (hh : 0 < h) :
    cutoffBandMultiplier h z = (aliasChart h).indicator (cutoffBandMultiplier h z) := by
  funext p
  by_cases hp : p ∈ aliasChart h
  · exact (Set.indicator_of_mem hp _).symm
  · rw [Set.indicator_of_notMem hp, cutoffBandMultiplier_zero_off_chart hh p hp]

theorem cutoffBandMultiplier_measurable {h z : ℝ} (D : Calibration h z) :
    AEStronglyMeasurable (fun p => (cutoffBandMultiplier h z p : ℂ)) (volume : Measure Space) := by
  have he : (fun p => (cutoffBandMultiplier h z p : ℂ)) =
      (aliasChart h).indicator (fun p => (cutoffBandMultiplier h z p : ℂ)) := by
    funext p
    by_cases hp : p ∈ aliasChart h
    · exact (Set.indicator_of_mem hp (fun p => (cutoffBandMultiplier h z p : ℂ))).symm
    · rw [Set.indicator_of_notMem hp, cutoffBandMultiplier_zero_off_chart D.h_pos p hp]
      rfl
  rw [he]
  exact (aestronglyMeasurable_indicator_iff (aliasChart_measurable h)).mpr
    ((Complex.continuous_ofReal.comp_continuousOn (cutoffBandMultiplier_continuousOn D)).aestronglyMeasurable
      (aliasChart_measurable h))

def cutoffAmplitudeData {h z : ℝ} (D : Calibration h z) :
    VectorMultiplier.Data (H := ℂ) (volume : Measure Space) 2 where
  coefficient p := (cutoffBandMultiplier h z p : ℂ)
  measurable := cutoffBandMultiplier_measurable D
  nonneg := by norm_num
  bound p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoffBandMultiplier_nonneg h z p)]
    exact cutoffBandMultiplier_le_two D p

def cutoffAmplitudeOperator {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] ScalarL2 :=
  (cutoffAmplitudeData D).operator

theorem cutoffAmplitudeOperator_ae {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    cutoffAmplitudeOperator D f =ᵐ[volume] fun p => (cutoffBandMultiplier h z p : ℂ) * f p := by
  filter_upwards [(cutoffAmplitudeData D).operator_ae f] with p hp
  exact hp.trans (mul_comm _ _)

theorem cutoffAmplitudeOperator_norm {h z : ℝ} (D : Calibration h z) :
    ‖cutoffAmplitudeOperator D‖ ≤ 2 := (cutoffAmplitudeData D).operator_norm_le

def Bh {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] FieldL2 :=
  (Qh h).comp ((Uh D.h_pos).comp (cutoffAmplitudeOperator D))

def bandGramOperator {h z : ℝ} (D : Calibration h z) : ScalarL2 →L[ℂ] ScalarL2 :=
  (Bh D)†.comp (Bh D)

theorem Bh_norm {h z : ℝ} (D : Calibration h z) : ‖Bh D‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖Qh h (Uh D.h_pos (cutoffAmplitudeOperator D f))‖ ≤ _
  calc
    _ ≤ ‖Uh D.h_pos (cutoffAmplitudeOperator D f)‖ :=
      by simpa only [one_mul] using (Qh h).le_of_opNorm_le (Qh_norm_le h) _
    _ ≤ ‖cutoffAmplitudeOperator D f‖ := Uh_norm_le D.h_pos _
    _ ≤ 2 * ‖f‖ := (cutoffAmplitudeOperator D).le_of_opNorm_le (cutoffAmplitudeOperator_norm D) f

theorem bandGramOperator_pairing {h z : ℝ} (D : Calibration h z) (f g : ScalarL2) :
    inner ℂ g (bandGramOperator D f) = inner ℂ (Bh D g) (Bh D f) := by
  change inner ℂ g (((Bh D)†) (Bh D f)) = _
  exact ContinuousLinearMap.adjoint_inner_right (Bh D) g (Bh D f)

#print axioms Bh_norm
#print axioms bandGramOperator_pairing

end Maxwell.Continuum.EffectiveMass
