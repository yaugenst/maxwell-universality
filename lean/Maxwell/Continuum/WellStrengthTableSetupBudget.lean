import Maxwell.Continuum.WellStrengthTableSetupPlan
import Maxwell.Continuum.WellStrengthPlan

/-! The measured allocation budget covers the semantic strength plan. In
particular, arbitrary unreduced calibration parts are charged by their actual
stored channels. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization.Table
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem parameters_width (parts : ℕ→Parts) (v : ℕ→ℕ)
    (same : ∀i∈parameterSources,v i=dataValues parts i) :
    bankWidth WellStrengthReset.parameters parts≤NatAssign.LengthSum.total parameterSources v:=by
  apply Finset.sup_le
  intro i hi
  have memberships : positivePort i∈parameterSources ∧ negativePort i∈parameterSources ∧
      denominatorPort i∈parameterSources:=by
    simp only [WellStrengthReset.parameters,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  apply max_le
  · have h:=NatAssign.LengthSum.member_le_total parameterSources v (positivePort i) memberships.1
    simpa only [same _ memberships.1,dataValues_positive] using h
  · apply max_le
    · have h:=NatAssign.LengthSum.member_le_total parameterSources v (negativePort i) memberships.2.1
      simpa only [same _ memberships.2.1,dataValues_negative] using h
    · have h:=NatAssign.LengthSum.member_le_total parameterSources v (denominatorPort i) memberships.2.2
      simpa only [same _ memberships.2.2,dataValues_denominator] using h

theorem physical_budget (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (data : WellStrengthPhysical.CalibratedParts p S hm) (v : ℕ→ℕ)
    (parts : ∀i∈parameterSources,v i=dataValues (WellStrengthPhysical.values p S hm data) i)
    (power : v 144=2^wellStoredPrecision p S hm)
    (diagonal : v 145=SourceGraph.Positive.base S (precision p S hm))
    (degree : v 143=4*SourceGraph.Positive.count S (precision p S hm)*(SourceGraph.Positive.width S (precision p S hm)+3))
    (original : v 141=(sourceCircuit S (precision p S hm)).size+(sourceCircuit S (precision p S hm)).size+
      (sourceSquareEntries S (precision p S hm)).length) :
    WellStrengthPhysical.minimumBudget p S hm data≤budget v:=by
  have retained:=parameters_width (WellStrengthPhysical.values p S hm data) v parts
  have maxbound : WellStrengthPhysical.retainedWidth p S hm data≤
      1+NatAssign.LengthSum.total parameterSources v:=by
    unfold WellStrengthPhysical.retainedWidth
    exact max_le (by omega) (by omega)
  have total : NatAssign.LengthSum.total sources v=
      NatAssign.LengthSum.total parameterSources v+NatAssign.LengthSum.total sourceSources v+
      NatAssign.LengthSum.total geometrySources v+NatAssign.LengthSum.total otherSources v:=by
    simp only [NatAssign.LengthSum.total,sources,List.map_append,List.sum_append,Nat.add_assoc]
  have metadata : NatAssign.LengthSum.total sourceSources v=(v 144).bits.length+(v 145).bits.length+
      (v 143).bits.length+(v 141).bits.length:=by
    simp [NatAssign.LengthSum.total,sourceSources,Nat.add_assoc]
  unfold WellStrengthPhysical.minimumBudget budget
  rw [total,metadata,power,diagonal,degree,original]
  omega

#print axioms physical_budget
end Maxwell.Continuum.WellStrengthInitialization.Table
