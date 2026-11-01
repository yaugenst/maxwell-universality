import Maxwell.Continuum.StoredSourceIdentity
import Maxwell.Continuum.StoredSourceMultiplierData
import Maxwell.Continuum.WellStrengthWellSerialization
import Maxwell.Cost.MagnitudeMax.SourceSemantics

/-! A source-list plan is derived from the actually stored geometry and
the original input promises. It contains only finite mathematical bounds. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

def sourceBankWidth (p : Source.Parameters) (S : Source.SparseSystem) (B : ℕ) : ℕ:=
  16*(B+1)+(2^sourcePrecision p S).bits.length+(sourcePrecision p S).bits.length+MagnitudeMax.inputWidth p S+2

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

def sourcePlan {saved} (physical : PhysicalValues p S hm data v saved) (hp : Source.Promises p S)
    (B : ℕ) {clock : List Bool} (hlen : clock.length=v 1250) {memory : ℕ→Bool}
    (stored : StoredGeometry saved (v 1252) (v 1250) memory) : SourcePayload.Plan (packedLength saved):=by
  have grow : Table.budget (Geometry.values v)≤geometryBudget v:=by unfold geometryBudget;omega
  have width : v 1250≤Table.budget (Geometry.values v):=by
    have hh:=Table.geometry_width (Geometry.values v)
    simpa only [Geometry.values_outside v 1250 (by decide)] using hh
  have packed : (packedLength saved).bits.length≤geometryBudget v:=by
    have hh:=Table.budget_width (Geometry.values v) 1253 (by decide)
    rw [Geometry.values_outside v 1253 (by decide),physical.packed] at hh
    exact hh.trans grow
  have fits : ∀i,((packedVector saved).get i).bits.length≤Table.budget (Geometry.values v):=
    fun i=>(stored.fits i).trans width
  have shift : (Geometry.values v 982).bits.length≤Table.budget (Geometry.values v):=
    Table.budget_width _ _ (by decide)
  have scales (j : Fin 3) : (Geometry.values v (983+j.val)).bits.length≤Table.budget (Geometry.values v):=by
    apply Table.budget_width
    fin_cases j <;> decide
  have inputCount:=(sourceCircuit S (RealizationParameters.precision p S hm)).circuit.inputs_le_size
  refine {
    data:=packedVector saved,base:=v 1252,slotWidth:=v 1250,geometryWidth:=geometryBudget v,
    bankWidth:=sourceBankWidth p S B,clock:=clock,constants:=Geometry.values v,
    source:=List.ofFn S.source,precision:=sourcePrecision p S,
    scalar:=(computedEnclosures p S hm).sourceScalar/Normalization.sourceScale S,
    template:=selectedTemplateBits p S hm,slotPositive:=stored.positive,slotBound:=width.trans grow,
    clockLength:=hlen,countWidth:=packed,fits:=stored.fits,
    baseValue:=(Geometry.output v).1,widthValue:=(Geometry.output v).2.1,
    oneValue:=(Geometry.output v).2.2.2.2.2.2.2.2.2.1,
    bankWidth_two:=by unfold sourceBankWidth;omega,
    powerWidth:=by unfold sourceBankWidth;omega,
    precisionWidth:=by unfold sourceBankWidth;omega,
    numeratorWidth:=?_,denominatorWidth:=?_,span:=?_,coordinates:=?_ }
  · intro q hq
    exact (MagnitudeMax.promised_rhs_width p S hp q hq).1.trans (by unfold sourceBankWidth;omega)
  · intro q hq
    exact (MagnitudeMax.promised_rhs_width p S hp q hq).2.trans (by unfold sourceBankWidth;omega)
  · simp only [List.length_ofFn]
    unfold packedLength
    omega
  · intro j _
    exact GeometryOutput.terminalCoordinate_bits _ _ _ fits shift scales _

theorem sourcePlan_bytes {saved} (physical : PhysicalValues p S hm data v saved) (hp : Source.Promises p S)
    (B : ℕ) {clock : List Bool} (hlen : clock.length=v 1250) {memory : ℕ→Bool}
    (stored : StoredGeometry saved (v 1252) (v 1250) memory)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm) :
    SourcePayload.streamBits (sourcePlan physical hp B hlen stored)=sourceStream p S hm:=by
  apply source_stream p S hm geometry (Geometry.values v)
    (by rw [Geometry.shift,length_eq,buffer_eq])
    (fun j=>by rw [Geometry.scale,length_eq,spacing_eq])
    ((Geometry.output v).2.2.2.2.2.1.trans length_eq)
    (sourcePlan physical hp B hlen stored) <;> rfl

#print axioms sourcePlan_bytes
end Maxwell.Continuum.WellStrengthInitialization
