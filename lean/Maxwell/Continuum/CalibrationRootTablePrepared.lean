import Maxwell.Continuum.CalibrationRootTableAllocationFrame

/-! The concrete coefficient-array initializer allocates its table and
restores the reusable evaluator state before entering the outer loop. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] storageValues storageWidth Profile.Runtime.memoryTable

abbrev preparedTable (v : ℕ→ℕ) (memory : ℕ→Bool) : PartArray.Table (2*(v 331)^3) :=
  Profile.Runtime.memoryTable (2*(v 331)^3) (storageWidth (v 331) (v 640) (v 345) (v 346))
    (v 347) (storageWidth_pos _ _ _ _) memory

def preparedMetadata (v : ℕ→ℕ) : ℕ :=
  storageWidth (v 331) (v 640) (v 345) (v 346)+(v 347).bits.length+
    (2*(v 331)^3).bits.length+(storageWidth (v 331) (v 640) (v 345) (v 346)).bits.length+4

def preparedCode : Code := .seq allocatedCode (NatAssign.code RootReset.naturalPlan)
def preparedChanged : Finset ℕ := allocatedChanged∪RootFrequency.changed
def preparedCost (v : ℕ→ℕ) (C H : ℕ) : ℕ :=
  allocatedCost (v 331) (v 640) (v 345) (v 346) C H+stageCost (storageNaturalWidth C)

theorem prepared_metadata (v : ℕ→ℕ) (memory : ℕ→Bool) :
    (preparedTable v memory).MetadataWidth (preparedMetadata v) := by
  apply Profile.Runtime.memoryTable_metadata
  · unfold preparedMetadata;omega
  · unfold preparedMetadata;omega

theorem prepared_fit (v : ℕ→ℕ) (memory : ℕ→Bool) :
    entryWidth (v 331) (v 640) (v 345) (v 346)≤addressValue (preparedTable v memory).width := by
  simpa only [preparedTable,Profile.Runtime.memoryTable,addressValue_bits] using
    entryWidth_le_storageWidth (v 331) (v 640) (v 345) (v 346)

theorem prepared_separated (v : ℕ→ℕ) (memory : ℕ→Bool) :
    (preparedTable v memory).Separated := Profile.Runtime.memoryTable_separated _ _ _ _ _

theorem prepared_executes (v : ℕ→ℕ) (C H : ℕ) (hC : 257≤C)
    (hw : ∀i∈allocationIds,(v i).bits.length≤C)
    (hzero : ∀i∈NaturalQuotient.workPorts,v i=0) (scale : Parts)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val)
    (hctx : Context RootReset.bank (v 640) v (RootReset.parts scale) s)
    (hz : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37) (h216 : Blank s.val 216)
    (hheaders : WordCleanup.Bounded Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape preparedCode cost s t ∧ cost≤preparedCost v C H ∧
      (preparedTable v s.val.memory).OutputReady t ∧
      Context RootReset.bank (v 640) (RootReset.naturals (v 331)) (RootReset.parts scale) t ∧
      Word t.val 570 (2*(v 331)^3) ∧ Blank t.val 216 ∧
      BinaryPrecision.Frame preparedChanged s.val t.val := by
  obtain ⟨c0,u,e0,h0,out,bank,bankMeta,z0,z216,f0⟩ := allocated_executes v C H hC hw input tape s hb hz
    (hctx.scratch 4 (by decide)) h7 h37 h216 hheaders
  have ctx0 := hctx.allocation_frame f0 bank z0
  obtain ⟨c1,t,e1,h1,bank1,z1,f1⟩ := RootReset.natural_executes (storageValues v) (storageNaturalWidth C)
    (fun i hi => storage_values_width v C hC hw i (Finset.mem_union_left _ hi))
    (storageValues_work_zero v hzero) input tape u ctx0.natural ctx0.scratch
  have ctx1 : Context RootReset.bank (v 640) (RootReset.naturals (v 331)) (RootReset.parts scale) t := by
    simpa only [storageValues_grid] using ctx0.natural_frame f1 bank1 z1
  have count0 : Word u.val 570 (2*(v 331)^3) := by
    have hh := bankMeta 570 (by decide)
    rw [(Calibration.PowerMachine.BufferNorm.Allocation.outputs (storageValues v)).2.2.2.2.1,
      (storageValues_outputs v).1] at hh
    exact hh
  exact ⟨c0+c1,t,e0.seq e1,by unfold preparedCost;omega,
    RootFrequency.output_frame out f1 z1,ctx1,
    word_of_eq (f1.tapes 570 (by decide)) count0,
    blank_of_eq (f1.tapes 216 (by decide)) z216,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)⟩

#print axioms prepared_executes
end Maxwell.Continuum.RationalDataflow.RootTable
