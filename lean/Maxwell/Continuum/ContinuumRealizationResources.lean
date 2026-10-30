import Maxwell.Continuum.ContinuumRealizationBudgets

/-! The chosen continuum precisions and literal fixed-width moment words
are linear in the input binary scale. The constants depend only on the
fixed source promise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  analysisBits inputBits Parameters.sourceMagnitude

def outputBitCoefficient (p : Source.Parameters) : ℕ :=
  analysisBits p+2*inputBits p+4*2^(9*Parameters.sourceMagnitude p)+
    180*Parameters.sourceMagnitude p+1024

private theorem affine_le_linear (a c ℓ : ℕ) (hℓ : 0 < ℓ) :
    a*ℓ+c ≤ (a+c)*ℓ := by nlinarith only [hℓ]

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

theorem templatePrecision_linear :
    templatePrecision p S ≤ (analysisBits p+6)*logSize S := by
  exact affine_le_linear _ _ _ (Parameters.inputLog_pos S.nnz)

theorem materialPrecision_linear :
    materialPrecision p S ≤ (analysisBits p+inputBits p+256)*logSize S := by
  have h := affine_le_linear (analysisBits p+inputBits p) 256 (logSize S)
    (Parameters.inputLog_pos S.nnz)
  simpa only [materialPrecision, scaleBits, Nat.add_mul] using h

theorem sourcePrecision_linear :
    sourcePrecision p S ≤ (analysisBits p+9)*logSize S := by
  have hℓ := Parameters.inputLog_pos S.nnz
  unfold sourcePrecision scaleBits
  nlinarith only [hℓ]

theorem momentPrecision_linear :
    momentPrecision p S ≤ (2*inputBits p+27)*logSize S := by
  have h := affine_le_linear (2*inputBits p) 27 (logSize S) (Parameters.inputLog_pos S.nnz)
  simpa only [momentPrecision, Nat.mul_assoc] using h

theorem calibrationPrecision_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    calibrationPrecision p S hm ≤
      (analysisBits p+4*2^(9*Parameters.sourceMagnitude p)+8)*logSize S := by
  have hd := (Parameters.source_scales p S hm hm2 hu).2.1
  change spacing p S hm ≤ 2^(9*Parameters.sourceMagnitude p)*logSize S at hd
  have hℓ := Parameters.inputLog_pos S.nnz
  unfold calibrationPrecision scaleBits
  nlinarith only [hd, hℓ]

theorem sourceTolerance_bits : Maxwell.rationalBitLength (sourceTolerance p S) ≤
    (analysisBits p+7)*logSize S := by
  rw [sourceTolerance, one_div, inv_pow, Parameters.inverse_two_pow_bits]
  simpa only [scaleBits, Nat.add_assoc] using
    affine_le_linear (analysisBits p) 7 (logSize S) (Parameters.inputLog_pos S.nnz)

theorem momentWordBits_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3 ≤
      (analysisBits p+2*inputBits p+34)*logSize S := by
  have hr := messageRangeBits_linear p S hm hm2 hu
  have hp := momentPrecision_linear p S
  have hℓ := Parameters.inputLog_pos S.nnz
  nlinarith only [hr, hp, hℓ]

theorem selected_precisions_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    energyPrecision p S hm ≤ outputBitCoefficient p*logSize S ∧
    templatePrecision p S ≤ outputBitCoefficient p*logSize S ∧
    materialPrecision p S ≤ outputBitCoefficient p*logSize S ∧
    sourcePrecision p S ≤ outputBitCoefficient p*logSize S ∧
    momentPrecision p S ≤ outputBitCoefficient p*logSize S ∧
    calibrationPrecision p S hm ≤ outputBitCoefficient p*logSize S ∧
    Maxwell.rationalBitLength (sourceTolerance p S) ≤ outputBitCoefficient p*logSize S ∧
    FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+3 ≤
      outputBitCoefficient p*logSize S := by
  have lift {a b : ℕ} (h : a ≤ b*logSize S) (hb : b ≤ outputBitCoefficient p) :
      a ≤ outputBitCoefficient p*logSize S := h.trans (Nat.mul_le_mul_right _ hb)
  refine ⟨lift (energyPrecision_linear p S hm hm2 hu) ?_,
    lift (templatePrecision_linear p S) ?_, lift (materialPrecision_linear p S) ?_,
    lift (sourcePrecision_linear p S) ?_, lift (momentPrecision_linear p S) ?_,
    lift (calibrationPrecision_linear p S hm hm2 hu) ?_, lift (sourceTolerance_bits p S) ?_,
    lift (momentWordBits_linear p S hm hm2 hu) ?_⟩ <;> unfold outputBitCoefficient <;> omega

theorem encodedMomentReport_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S))
    (v w : ℚ) (hv : |v| ≤ 1) (hw : |w| ≤ 8*inverseBound p S hm*S.nnz) :
    Maxwell.unsignedBitLength
      (FiniteAuxiliary.encodedMomentReport (inverseBound p S hm) S.nnz (momentPrecision p S)
        v w hv hw).val ≤ outputBitCoefficient p*logSize S :=
  (FiniteAuxiliary.encodedMomentReport_bits _ _ _ _ _ _ _).trans
    (selected_precisions_linear p S hm hm2 hu).2.2.2.2.2.2.2

theorem moment_serial_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S))
    (w : Fin (2^(FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+
      momentPrecision p S+3))) :
    (FiniteAuxiliary.momentWordSerial
      (FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) w).length ≤
        outputBitCoefficient p*logSize S := by
  rw [FiniteAuxiliary.momentWordSerial_length]
  exact (selected_precisions_linear p S hm hm2 hu).2.2.2.2.2.2.2

theorem moment_stream_linear (hm2 : 2 ≤ S.nnz) (hu : IsUnit (Source.realMatrix S))
    (w : Fin (sites p S hm) → Fin (2^(FiniteAuxiliary.messageRangeBits
      (inverseBound p S hm) S.nnz+momentPrecision p S+3))) :
    (FiniteAuxiliary.momentStream
      (FiniteAuxiliary.messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) w).length ≤
        sites p S hm*(outputBitCoefficient p*logSize S) := by
  rw [FiniteAuxiliary.momentStream_length]
  exact Nat.mul_le_mul_left _ (selected_precisions_linear p S hm hm2 hu).2.2.2.2.2.2.2

#print axioms selected_precisions_linear
#print axioms encodedMomentReport_linear
#print axioms moment_stream_linear

end Maxwell.Continuum.RealizationParameters
