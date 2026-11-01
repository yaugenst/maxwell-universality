import Maxwell.Continuum.WellStrengthInitialize
import Maxwell.Continuum.WellStrengthTableSetupBudget

/-! Semantic use of the executed initializer. Both the original strength
state and the geometry serializer context are derived from its actual output. -/
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition
open RationalDataflow SourceDecorationEnumeration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def preparedTable (v : ℕ→ℕ) (J : ℕ) (memory : ℕ→Bool) : PartArray.Table J:=
  Profile.Runtime.memoryTable J (Table.slotWidth (Geometry.values v)) (v 2600)
    (Table.slot_positive (Geometry.values v)) memory

theorem Result.original_state {v : ℕ→ℕ} {n J : ℕ} {q : WellOriginalPass.Plan n J}
    {clock : List Bool} {memory : ℕ→Bool} {s : Store}
    (h : Result v q.values clock memory s)
    (hprecision : v 990=q.precision) (hpower : v 144=2^q.precision)
    (hbudget : q.budget=Table.budget (Geometry.values v))
    (hmetadata : q.metadataBudget=Table.metadataBudget (Geometry.values v))
    (hcount : v 1209=J) (horiginal : v 141=n)
    (hdiagonal : v 145=q.diagonalBase) (hdegree : v 143=q.degreeBase)
    (habove : q.prefixLimit≤v 2600)
    (diagonals : BitArray.Represents s.val.memory q.diagonalBase 4 q.diagonalWords)
    (degrees : BitArray.Represents s.val.memory q.degreeBase 2 q.degreeWords)
    (saved : ∀j,j<q.prefixLimit→s.val.memory j=memory j) :
    WellOriginalPass.State q (preparedTable v J memory) 0 memory s:=by
  subst J
  have heap : Geometry.values v 2600=v 2600:=Geometry.values_outside v 2600 (by decide)
  have table := h.table
  simp only [Table.table,heap] at table
  have metadata := Table.metadata (Geometry.values v) memory
  simp only [Table.table,heap] at metadata
  refine ⟨h.rational,h.clean,?_,table,?_,?_,?_,?_,diagonals,degrees,?_,?_,?_,?_,?_,?_,?_,saved⟩
  · simpa only [hpower] using h.power
  · rw [hmetadata]
    exact metadata
  · simp only [preparedTable,Profile.Runtime.memoryTable,addressValue_bits,Table.slotWidth,
      Geometry.values_outside v 990 (by decide),hprecision,hbudget]
    exact le_rfl
  · exact Profile.Runtime.memoryTable_separated (v 1209) _ _ _ _
  · simp only [preparedTable,Profile.Runtime.memoryTable,addressValue_bits]
    exact ⟨habove,by omega,by omega⟩
  · have word := h.geometry 993 (by decide)
    simpa only [(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.1,hdiagonal] using word
  · have word := h.geometry 994 (by decide)
    simpa only [(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.2.1,hdegree] using word
  · have word := h.geometry 998 (by decide)
    simpa only [(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using word
  · have word := h.geometry 999 (by decide)
    simpa only [(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] using word
  · intro i hi
    have cases : i=995 ∨ i=996:=by simpa only [WellSourceRead.metaIds,Finset.mem_insert,Finset.mem_singleton] using hi
    rcases cases with rfl|rfl
    · simpa only [WellOriginalPass.readerValues,(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.2.2.1] using h.geometry 995 (by decide)
    · simpa only [WellOriginalPass.readerValues,(Geometry.output v).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] using h.geometry 996 (by decide)
  · simpa only [(Geometry.output v).2.2.2.2.2.2.2.2.2.2.1] using h.geometry 988 (by decide)
  · simpa only [(Geometry.output v).2.2.1,horiginal] using h.geometry 963 (by decide)

theorem Result.geometry_context {v : ℕ→ℕ} {parts : ℕ→Parts} {clock : List Bool}
    {memory : ℕ→Bool} {s : Store} (h : Result v parts clock memory s)
    {n e : ℕ} (saved : SourceEmission.Geometry n e)
    (stored : StoredGeometry saved (v 1252) (v 1250) s.val.memory) :
    GeometryOutput.Context (packedVector saved) (v 1252) (v 1250)
      (Table.budget (Geometry.values v)) clock (Geometry.values v) (Geometry.values v) s:=by
  refine ⟨⟨?_,h.table.scratch,h.table.seven⟩,?_,stored.stored,h.clockWord,fun _ _=>rfl⟩
  · intro i hi
    exact h.geometry i (Finset.mem_union_left _ hi)
  · intro i hi
    have subset : GeometryOutput.ids⊆Table.sources.toFinset:=by decide
    exact Table.budget_width (Geometry.values v) i (by simpa only [List.mem_toFinset] using subset hi)

#print axioms Result.original_state
#print axioms Result.geometry_context
end Maxwell.Continuum.WellStrengthInitialization
