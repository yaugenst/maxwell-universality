import Maxwell.Continuum.WellStrengthGeometrySetup
import Maxwell.Continuum.WellStrengthTableSetup
import Maxwell.Continuum.WellOriginalPassData
import Maxwell.Cost.BankArray.Frame

/-! The strength initializer copies the computed geometry metadata, allocates
its actual rational table, then clears obsolete source descriptor tapes used
by rounding. Source arrays and packed geometry remain in the same memory. -/
namespace Maxwell.Continuum.WellStrengthInitialization
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def inputs : Finset ℕ := Geometry.inputs∪(Table.sources.toFinset\Geometry.targets)
def cleanHeaders : List ℕ := [4,140,142,143,220,221,222,223]
def work : Finset ℕ := Geometry.work∪Table.work∪cleanHeaders.toFinset
def code : Code := .seq Geometry.code (.seq Table.code (WordCleanup.code cleanHeaders))
def costBound (v : ℕ→ℕ) (B H clockLength : ℕ) : ℕ := Geometry.costBound B H clockLength+
  (Table.costBound (Geometry.values v) (2^30*(B+1)) H+cleanHeaders.length*(6*H+4)+1)

theorem inputs_ge (i : ℕ) (hi : i∈inputs) : 4 ≤ i :=by
  rcases Finset.mem_union.mp hi with ha|ha
  · exact Geometry.ids_ge i (Finset.mem_union_left _ ha)
  · exact Table.ids_ge i (Finset.mem_union_left _ (Finset.mem_sdiff.mp ha).1)

end Maxwell.Continuum.WellStrengthInitialization
