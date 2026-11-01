import Maxwell.Continuum.StoredReadoutIdentity
import Maxwell.Continuum.WellStrengthWellSerialization

/-! Actual continuum readout placement serialization from the produced
geometry context and retained source dimension/circuit-size words. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem readouts_executes {saved} (physical : PhysicalValues p S hm data v saved)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store} {gv : ℕ→ℕ}
    (g : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
      clock (Geometry.values v) gv s)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (firstWord : Word s.val 503 (sourceCircuit S (RealizationParameters.precision p S hm)).size)
    (countWord : Word s.val 500 S.n)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) (hOld : old.length≤geometryBudget v)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape GeometryOutput.Readout.code cost s t ∧
      cost≤GeometryOutput.Readout.costBound (geometryBudget v) S.n ∧
      GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
        clock (Geometry.values v) w t ∧
      t.val.output=(readoutPlacementStream p S hm).reverse++s.val.output ∧
      GeometryOutput.OutputFrame GeometryOutput.Readout.work s.val t.val ∧
      ∃last : List Bool,last.length=S.n.bits.length ∧BankArray.Word t.val 972 last:=by
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
  have hn := (sourceCircuit S (RealizationParameters.precision p S hm)).circuit.inputs_le_size
  have hspan : 3*(sourceCircuit S (RealizationParameters.precision p S hm)).size+3*S.n≤packedLength saved:=by
    unfold packedLength
    omega
  have firstBound : (sourceCircuit S (RealizationParameters.precision p S hm)).size.bits.length≤geometryBudget v:=by
    have hfirst : (sourceCircuit S (RealizationParameters.precision p S hm)).size≤packedLength saved:=by omega
    have hh:=Nat.size_le_size hfirst
    rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at hh
    exact hh.trans packed
  have countBound : S.n.bits.length≤geometryBudget v:=by
    have hh:=Nat.size_le_size hn
    rw [←Nat.size_eq_bits_len,←Nat.size_eq_bits_len] at hh
    exact hh.trans firstBound
  obtain ⟨cost,t,w,ex,hc,gt,_,out,mem,last⟩:=GeometryOutput.Readout.executes g stored.positive (width.trans grow)
    hlen packed stored.fits (Geometry.output v).1 (Geometry.output v).2.1
    (Geometry.output v).2.2.2.2.2.2.2.2.2.1
    (sourceCircuit S (RealizationParameters.precision p S hm)).size S.n firstBound countBound
    (Geometry.output v).2.2.2.2.2.2.2.2.1 hspan
    (fun _ _=>GeometryOutput.terminalCoordinate_bits _ _ _ fits shift scales _)
    firstWord countWord old hold hOld input tape
  have identity:=readout_stream p S hm geometry (Geometry.values v)
    (by rw [Geometry.shift,length_eq,buffer_eq])
    (fun j=>by rw [Geometry.scale,length_eq,spacing_eq])
    ((Geometry.output v).2.2.2.2.2.1.trans length_eq)
  exact ⟨cost,t,w,ex,hc,gt,by simpa only [identity] using out,mem,last⟩

#print axioms readouts_executes
end Maxwell.Continuum.WellStrengthInitialization
