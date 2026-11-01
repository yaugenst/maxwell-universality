import Maxwell.Continuum.StoredDecoderInitialize
import Maxwell.Continuum.StoredDecoderDescriptionData
import Maxwell.Continuum.WellStrengthWellSerialization

/-! The decoder row plan is derived from the produced packed geometry,
the generated strength table, and the executed natural selectors. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def decoderSelectorBudget (nv : ℕ→ℕ) : ℕ:=
  (nv 500).bits.length+(nv 4701).bits.length+(nv 4702).bits.length+(nv 4703).bits.length+
  (nv 4705).bits.length+(nv 4706).bits.length+(nv 4707).bits.length+(nv 4708).bits.length

theorem decoderSelectorBudget_width (nv : ℕ→ℕ) (i : ℕ)
    (hi : i∈({500,4701,4702,4703}:Finset ℕ)∪DecoderRow.selectorPorts) :
    (nv i).bits.length≤decoderSelectorBudget nv:=by
  simp only [DecoderRow.selectorPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl) <;> unfold decoderSelectorBudget <;> omega

def decoderConstants (v nv : ℕ→ℕ) (P i : ℕ) : ℕ:=
  if i=144 then 2^P else if i∈DecoderRow.selectorPorts then nv i else Geometry.values v i

def decoderBankWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (v nv : ℕ→ℕ) (R M : ℕ) : ℕ:=
  2+geometryBudget v+R+M+Table.metadataBudget (Geometry.values v)+
    decoderSelectorBudget nv+(2^wellStoredPrecision p S hm).bits.length

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v nv : ℕ→ℕ}

def decoderPlan {saved} (physical : PhysicalValues p S hm data v saved)
    (table : PartArray.Table (siteCount saved)) (R M H : ℕ) (metadata : table.MetadataWidth M)
    (scale : (nv 4707:ℚ)/(nv 4708)=normalizationScale S) (hb : S.source≠0)
    {clock : List Bool} (hlen : clock.length=v 1250) {memory : ℕ→Bool}
    (stored : StoredGeometry saved (v 1252) (v 1250) memory) :
    DecoderRow.Plan (packedLength saved) (siteCount saved):=by
  have grow : Table.budget (Geometry.values v)≤geometryBudget v:=by unfold geometryBudget;omega
  have width : v 1250≤Table.budget (Geometry.values v):=by
    simpa only [Geometry.values_outside v 1250 (by decide)] using Table.geometry_width (Geometry.values v)
  have packed : (packedLength saved).bits.length≤geometryBudget v:=by
    have hh:=Table.budget_width (Geometry.values v) 1253 (by decide)
    rw [Geometry.values_outside v 1253 (by decide),physical.packed] at hh
    exact hh.trans grow
  have positive : 0<nv 4708:=by
    have hp : (0:ℚ)<normalizationScale S:=
      div_pos (Normalization.sourceScale_pos S hb) (Normalization.matrixScale_pos S hm)
    by_contra hz
    have zero : nv 4708=0:=by omega
    rw [zero,Nat.cast_zero,div_zero] at scale
    rw [←scale] at hp
    exact (lt_irrefl 0) hp
  exact {
    data:=packedVector saved,table:=table,base:=v 1252,slotWidth:=v 1250,
    geometryWidth:=geometryBudget v,bankWidth:=decoderBankWidth p S hm v nv R M,workspaceWidth:=H,
    clock:=clock,geometryConstants:=Geometry.values v,
    constants:=decoderConstants v nv (wellStoredPrecision p S hm),
    slotPositive:=stored.positive,slotBound:=width.trans grow,clockLength:=hlen,
    countWidth:=packed,fits:=stored.fits,baseValue:=(Geometry.output v).1,widthValue:=(Geometry.output v).2.1,
    oneValue:=(Geometry.output v).2.2.2.2.2.2.2.2.2.1,
    bankWidth_two:=by unfold decoderBankWidth;omega,
    geometry_bank:=by unfold decoderBankWidth;omega,
    tableWidth:=metadata.mono (by unfold decoderBankWidth;omega),
    indexWidth:=physical.metadata.trans (by unfold decoderBankWidth;omega),
    powerPositive:=by simp only [decoderConstants,ite_true];positivity,
    scalePositive:=by simpa [decoderConstants,DecoderRow.selectorPorts] using positive }

theorem decoderPlan_fixed {n base width G : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {gv : ℕ→ℕ} {rv : ℕ→Parts} {s : Store} (P : ℕ)
    (g : GeometryOutput.Context values base width G clock (Geometry.values v) gv s) :
    ∀i∈DecoderRow.constantPorts,DecoderRow.initialValues gv nv rv P i=decoderConstants v nv P i:=by
  intro i hi
  simp only [DecoderRow.constantPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [DecoderRow.initialValues,DecoderRow.outputs,DecoderRow.selectorPorts,
    decoderConstants,Finset.mem_insert,Finset.mem_singleton]; norm_num
  all_goals exact g.fixed _ (by decide)

#print axioms decoderPlan_fixed
end Maxwell.Continuum.WellStrengthInitialization
