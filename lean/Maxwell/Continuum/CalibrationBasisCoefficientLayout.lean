import Maxwell.Continuum.CalibrationBasisCoefficientInput

/-! The allocated coefficient destination is disjoint from the generated
basis source, and its measured budget bounds the actual source descriptors. -/
namespace Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
attribute [local irreducible] bank sourceTable CoefficientAllocation.budget
  CoefficientAllocation.slotWidth CoefficientAllocation.slotOffset

theorem headers (R heap : ℕ) (nf extra work : ℕ→ℕ) :
    numbers R heap nf extra work 200=625 ∧ numbers R heap nf extra work 202=heap ∧
    numbers R heap nf extra work 203=heap+aliasArraySize R*625 ∧
    numbers R heap nf extra work 204=heap+2*aliasArraySize R*625 := by
  have h200:(200:ℕ)∉naturalIds:=natural_outside _ (by decide) (by decide) (by decide) (by decide)
  have h202:(202:ℕ)∉naturalIds:=natural_outside _ (by decide) (by decide) (by decide) (by decide)
  have h203:(203:ℕ)∉naturalIds:=natural_outside _ (by decide) (by decide) (by decide) (by decide)
  have h204:(204:ℕ)∉naturalIds:=natural_outside _ (by decide) (by decide) (by decide) (by decide)
  simp only [numbers,h200,h202,h203,h204,show (200:ℕ)≠311 by decide,
    show (202:ℕ)≠311 by decide,show (203:ℕ)≠311 by decide,show (204:ℕ)≠311 by decide,
    show (202:ℕ)≠200 by decide,show (203:ℕ)≠200 by decide,show (204:ℕ)≠200 by decide,
    show (203:ℕ)≠202 by decide,show (204:ℕ)≠202 by decide,show (204:ℕ)≠203 by decide,
    ↓reduceIte,and_self]

theorem heap_end (R heap : ℕ) (nf extra work : ℕ→ℕ) :
    CoefficientAllocation.heap (numbers R heap nf extra work)=heap+3*aliasArraySize R*625 := by
  rw [CoefficientAllocation.heap,(headers R heap nf extra work).1,
    (headers R heap nf extra work).2.2.2,radius]
  ring

theorem source_metadata (R heap : ℕ) (nf extra work : ℕ→ℕ) (memory : ℕ→Bool)
    (a : Table (aliasArraySize R)) (hm:sameMetadata (sourceTable R heap memory) a) :
    a.MetadataWidth (CoefficientAllocation.budget (numbers R heap nf extra work)) := by
  let n:=numbers R heap nf extra work
  have w:=CoefficientAllocation.budget_bound n 200 (by decide)
  have p:=CoefficientAllocation.budget_bound n 202 (by decide)
  have q:=CoefficientAllocation.budget_bound n 203 (by decide)
  have d:=CoefficientAllocation.budget_bound n 204 (by decide)
  have bound:=CoefficientAllocation.budget_ge n
  dsimp only [n] at w p q d
  rw [(headers R heap nf extra work).1] at w
  rw [(headers R heap nf extra work).2.1] at p
  rw [(headers R heap nf extra work).2.2.1] at q
  rw [(headers R heap nf extra work).2.2.2] at d
  exact ⟨by simpa only [hm.1,sourceTable,Profile.Runtime.memoryTable] using w,
    by simpa only [hm.2.1,sourceTable,Profile.Runtime.memoryTable] using p,
    by simpa only [hm.2.2.1,sourceTable,Profile.Runtime.memoryTable] using q,
    by simpa only [hm.2.2.2.1,sourceTable,Profile.Runtime.memoryTable] using d,
    by simpa only [hm.2.2.2.2,sourceTable,Profile.Runtime.memoryTable,List.length_replicate] using
      (show 625≤CoefficientAllocation.budget n by omega)⟩

theorem coefficient_layout (n : ℕ→ℕ) (memory : ℕ→Bool) :
    SourceLayout (CoefficientAllocation.table n memory) (CoefficientAllocation.heap n) := by
  constructor <;> simp only [CoefficientAllocation.table,Profile.Runtime.memoryTable,addressValue_bits]

theorem coefficient_metadata (n : ℕ→ℕ) (left right : ℕ→Bool) :
    sameMetadata (CoefficientAllocation.table n left) (CoefficientAllocation.table n right) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem coefficient_separated (n : ℕ→ℕ) (memory : ℕ→Bool) :
    (CoefficientAllocation.table n memory).Separated :=
  Profile.Runtime.memoryTable_separated _ _ _ _ _

theorem coefficient_width (n : ℕ→ℕ) (memory : ℕ→Bool) :
    addressValue (CoefficientAllocation.table n memory).width=CoefficientAllocation.slotWidth (CoefficientAllocation.budget n) := by
  simp only [CoefficientAllocation.table,Profile.Runtime.memoryTable,addressValue_bits]

theorem separated (R heap : ℕ) (nf extra work : ℕ→ℕ) (old memory : ℕ→Bool)
    (a : Table (aliasArraySize R)) (hm:sameMetadata (sourceTable R heap old) a) :
    a.SeparatedFrom (CoefficientAllocation.table (numbers R heap nf extra work) memory) := by
  have h:=Profile.Runtime.memoryTable_separatedFrom (aliasArraySize R)
    (tableSize (aliasArraySize R)) 625 (CoefficientAllocation.slotWidth
      (CoefficientAllocation.budget (numbers R heap nf extra work))) heap
    (CoefficientAllocation.heap (numbers R heap nf extra work)) (by decide)
    (CoefficientAllocation.slotWidth_pos _) memory (by rw [heap_end])
  simpa only [PartArray.Table.SeparatedFrom,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,
    sourceTable,CoefficientAllocation.table,Profile.Runtime.memoryTable,radius] using h

#print axioms source_metadata
#print axioms separated
end Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
