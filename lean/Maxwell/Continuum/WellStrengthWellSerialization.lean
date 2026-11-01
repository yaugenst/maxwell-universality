import Maxwell.Continuum.WellStrengthFromStoredInputs
import Maxwell.Continuum.StoredChronologicalWells
import Maxwell.Continuum.StoredGeometryBounds
import Maxwell.Cost.BankArray.Unique
import Maxwell.Cost.Structured.MemoryFootprint

/-! The concrete chronological serializer consumes the produced numerator
array and emits the exact physical well records, including placements and
the retained common profile and template bytes. -/
noncomputable section
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition Maxwell.Logical Maxwell.Logical.Routing
open RationalDataflow RealizationParameters SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

def geometryBudget (v : ℕ→ℕ) : ℕ := 2*Table.budget (Geometry.values v)+2

theorem geometry_widen {v : ℕ→ℕ} {n base width : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s : Store}
    (g : GeometryOutput.Context data base width (Table.budget (Geometry.values v)) clock constants gv s) :
    GeometryOutput.Context data base width (geometryBudget v) clock constants gv s:=
  ⟨g.ready,fun i hi=>(g.wordWidth i hi).trans (by unfold geometryBudget;omega),g.array,g.clockWord,g.fixed⟩

theorem wellCode_memory : WellOutput.code.protectsMemory=true:=by decide +kernel

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
variable {data : WellStrengthPhysical.CalibratedParts p S hm} {v : ℕ→ℕ}

theorem serialize {saved} (physical : PhysicalValues p S hm data v saved)
    (geometry : Represents S (RealizationParameters.precision p S hm) saved)
    (length_eq : v 2221=length p S hm) (spacing_eq : v 2227=spacing p S hm)
    (buffer_eq : v 2244=bufferSteps p S hm)
    {clock : List Bool} (hlen : clock.length=v 1250) {s : Store} {gv : ℕ→ℕ}
    (g : GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (Table.budget (Geometry.values v))
      clock (Geometry.values v) gv s)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory)
    (table : PartArray.Table (siteCount saved))
    (correct : ∀i:Fin (siteCount saved),table.get i=Parts.literal (wellNumerators p S hm i.val:ℚ))
    (H : ℕ) (metadata : table.MetadataWidth (Table.metadataBudget (Geometry.values v)+H+1))
    (payload : WellPayload.State table (wellStoredPrecision p S hm) (Table.metadataBudget (Geometry.values v)+H+1)
      0 (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm)
      (WellStrengthPhysical.values p S hm data) s)
    (total : Word s.val 988 (siteCount saved)) (outer : Blank s.val 972) (inner : Blank s.val 973)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w r,Executes input tape WellOutput.code cost s t ∧
      cost≤WellOutput.costBound (geometryBudget v) (Table.metadataBudget (Geometry.values v)+H+1)
        saved.original.size saved.paths.size (packedLength saved)
        (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) ∧
      t.val.output=(chronologicalWellStream p S hm).reverse++s.val.output ∧
      t.val.memory=s.val.memory ∧
      GeometryOutput.Context (packedVector saved) (v 1252) (v 1250) (geometryBudget v)
        clock (Geometry.values v) w t ∧ w 971=packedLength saved ∧
      WellPayload.State table (wellStoredPrecision p S hm) (Table.metadataBudget (Geometry.values v)+H+1)
        (siteCount saved) (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm) r t ∧
      WordCleanup.Bounded [972,973] (geometryBudget v) t.val:=by
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
  have count : gv 988=siteCount saved:=by
    have same:=BankArray.word_unique (g.ready.bank 988 (by decide)) total
    simpa only [addressValue_bits] using congrArg addressValue same
  have pwidth : (wellStoredPrecision p S hm).bits.length≤Table.metadataBudget (Geometry.values v)+H+1:=by
    have small : (wellStoredPrecision p S hm).bits.length≤wellStoredPrecision p S hm:=by
      rw [Nat.size_eq_bits_len,Nat.size_le];exact Nat.lt_two_pow_self
    unfold Table.metadataBudget Table.slotWidth
    rw [Geometry.values_outside v 990 (by decide),physical.precision_eq]
    omega
  obtain ⟨cost,t,word,origin,w,r,inside,ex,hc,gt,ix,pt,output,wordEq,wordLen,insideWord,insideLen⟩:=WellOutput.executes saved
    (geometry_widen g) stored.positive (width.trans grow) hlen packed stored.fits
    (Geometry.output v).1 (Geometry.output v).2.1 (Geometry.output v).2.2.2.2.2.2.2.2.2.1
    ((Geometry.output v).2.2.1.trans physical.original) ((Geometry.output v).2.2.2.1.trans physical.edges)
    (Geometry.output v).2.2.2.2.2.2.2.2.1 count (packedLength saved)
    (Represents.path_length_two S (RealizationParameters.precision p S hm) geometry)
    (fun i=>by have span:=pathOffset_span saved i;omega)
    (GeometryOutput.terminalCoordinate_bits _ _ _ fits shift scales)
    (GeometryOutput.mediatorCoordinate_bits _ _ _ fits shift scales)
    table (wellNumerators p S hm) correct (wellStoredPrecision p S hm)
    (Table.metadataBudget (Geometry.values v)+H+1) metadata pwidth (physical.metadata.trans (by omega))
    (Profile.profileBits (materialPrecision p S)) (selectedTemplateBits p S hm)
    (WellStrengthPhysical.values p S hm data) payload [] []
    ((RationalAccumulator.zero_word_iff_blank _ _).mpr outer) (by simp)
    ((RationalAccumulator.zero_word_iff_blank _ _).mpr inner) (by simp) input tape
  have bits := storedBits_eq_chronological p S hm geometry (Geometry.values v)
    (by rw [Geometry.shift,length_eq,buffer_eq])
    (fun j=>by rw [Geometry.scale,length_eq,spacing_eq])
    ((Geometry.output v).2.2.2.2.2.1.trans length_eq)
  refine ⟨cost,t,w,r,ex,hc,by simpa only [bits] using output,ex.protectsMemory wellCode_memory,gt,ix,pt,?_⟩
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl
  · refine ⟨word,?_,origin,wordEq⟩
    rw [wordLen]
    have hh:=Table.budget_width (Geometry.values v) 964 (by decide)
    rw [(Geometry.output v).2.2.2.1,physical.edges] at hh
    exact hh.trans grow
  · exact ⟨inside,insideLen,insideWord⟩

#print axioms serialize
end Maxwell.Continuum.WellStrengthInitialization
