import Maxwell.Continuum.StoredSourceSetup
import Maxwell.Continuum.WellStrengthPlan

/-! The common multiplier's reciprocal side conditions and exact value
follow from the actual calibration and source normalization definitions. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Logical RationalDataflow
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
attribute [local irreducible] computedEnclosures Parameters.sourceInput MasterConstants.exponent

theorem calibrated_mode_nonzero (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) :
    (WellStrengthPhysical.values p S hm data 1).value≠0:=by
  rw [WellStrengthPhysical.midpoint]
  have low:=(computedEnclosures p S hm).mode_lower_ge_one
  have ordered:=(computedEnclosures p S hm).mode.ordered
  unfold Maxwell.Certificate.Interval.midpoint
  linarith

theorem source_multiplier_value (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hb : S.source≠0) (data : WellStrengthPhysical.CalibratedParts p S hm) :
    (SourcePayload.multiplierValues (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2
      (WellStrengthPhysical.values p S hm data) 13).value=
      (computedEnclosures p S hm).sourceScalar/Normalization.sourceScale S:=by
  have good : Good SourcePayload.bank (WellStrengthPhysical.values p S hm data):=
    fun i hi=>WellStrengthPhysical.good p S hm data i ((by decide : SourcePayload.bank⊆WellStrength.bank) hi)
  rw [SourcePayload.multiplier_value _ _ _ good (calibrated_mode_nonzero p S hm data)
    (NormalizeRatio.sourceScalePair_positive S hb).1 (NormalizeRatio.sourceScalePair_positive S hb).2,
    WellStrengthPhysical.scale,WellStrengthPhysical.midpoint,NormalizeRatio.sourceScalePair_value]
  rfl

#print axioms source_multiplier_value
end Maxwell.Continuum.RealizationParameters
