import Maxwell.Continuum.EffectiveMassConstantScaling
import Maxwell.Continuum.EffectiveMassPacketDifference

/-! The actual Maxwell packet factor is close to the literal spatial
effective-mass reconstruction, including its high-momentum tail. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary

attribute [local irreducible] referenceScalarOperator angularFourier envelopeOperator

theorem constantPacketReconstruction_apply {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    constantPacketReconstruction hh f = envelopeOperator hh
      (Well.rootProfile.multiplier ((angularFourier ℂ).symm
        (packetMask h (referenceScalarOperator f)))) := by
  change Qh h (constantUh hh (referenceScalarOperator f)) = _
  rw [constantUh_eq_envelope, Qh_envelope]

theorem referenceReconstruction_apply {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    referenceReconstruction hh f = envelopeOperator hh
      (Well.rootProfile.multiplier ((angularFourier ℂ).symm (referenceScalarOperator f))) := rfl

theorem constantPacket_tail_error {h z : ℝ} (D : Calibration h z) :
    ‖constantPacketReconstruction D.h_pos - referenceReconstruction D.h_pos‖ ≤ (2 : ℝ)^96 * h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) D.h_pos.le)
  intro f
  change ‖constantPacketReconstruction D.h_pos f - referenceReconstruction D.h_pos f‖ ≤ _
  rw [constantPacketReconstruction_apply, referenceReconstruction_apply, ← map_sub,
    ← map_sub, ← map_sub]
  have he : packetMask h (referenceScalarOperator f) - referenceScalarOperator f =
      -(packetReferenceTail h f) := by
    change _ = -(referenceScalarOperator f - packetMask h (referenceScalarOperator f))
    abel
  rw [he, map_neg, map_neg, map_neg, norm_neg]
  calc
    _ ≤ 32 * ‖Well.rootProfile.multiplier ((angularFourier ℂ).symm (packetReferenceTail h f))‖ :=
      (envelopeOperator D.h_pos).le_of_opNorm_le (envelopeOperator_norm D.h_pos) _
    _ ≤ 32 * ‖(angularFourier ℂ).symm (packetReferenceTail h f)‖ :=
      mul_le_mul_of_nonneg_left (Well.rootProfile.multiplier_apply_norm_le _) (by norm_num)
    _ = 32 * ‖packetReferenceTail h f‖ := by rw [(angularFourier ℂ).symm.norm_map]
    _ ≤ 32 * (((2 : ℝ)^91 * h) * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        ((packetReferenceTail h).le_of_opNorm_le (packetReferenceTail_norm D) f) (by norm_num)
    _ = _ := by ring

theorem Bh_reconstruction_error {h z : ℝ} (D : Calibration h z) :
    ‖Bh D - referenceReconstruction D.h_pos‖ ≤ (2 : ℝ)^131 * h := by
  have ht := norm_add_le (Bh D - constantPacketReconstruction D.h_pos)
    (constantPacketReconstruction D.h_pos - referenceReconstruction D.h_pos)
  rw [sub_add_sub_cancel] at ht
  have hb := add_le_add (Bh_constantPacket_error D) (constantPacket_tail_error D)
  calc
    _ ≤ (2 : ℝ)^130 * h + (2 : ℝ)^96 * h := ht.trans hb
    _ ≤ _ := by nlinarith [D.h_pos]

end Maxwell.Continuum.EffectiveMass
