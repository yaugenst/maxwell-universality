import Maxwell.Continuum.WellStrengthGeometrySetupPlan
import Maxwell.Cost.Structured.NatAssign.LengthSum
import Maxwell.Continuum.CalibrationNormalizationAllocation

/-! Measured allocation of the strength table. The budget scans the actual
calibration parts and source descriptors; the next free heap address is an
input from the preceding allocation. -/
namespace Maxwell.Continuum.WellStrengthInitialization.Table
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-- The five retained rational parts, with all three natural channels. -/
def parameterSources : List ℕ := [1003,1004,1005,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023]
def sourceSources : List ℕ := [144,145,143,141]
def geometrySources : List ℕ := [960,961,963,964,965,966,967,968,969,970,971,974,975,976,977,
  978,979,980,981,982,983,984,985,986,987,988,989]
def otherSources : List ℕ := [990,1209,1250,1253,2600]
def sources : List ℕ := parameterSources++sourceSources++geometrySources++otherSources
def clearHeaders : List ℕ := [570,571,572,573,2606,2607,2608]
def ids : Finset ℕ := sources.toFinset∪clearHeaders.toFinset
def changed : Finset ℕ := {0,1,2,3,570,571,572,573,2606,2607,2608}
def loaded (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈clearHeaders then 0 else v i
def budget (v : ℕ→ℕ) : ℕ := 5+NatAssign.LengthSum.total sources v+v 1250
def slotWidth (v : ℕ→ℕ) : ℕ := v 990+4096*(256*(budget v+1))+4179

def plan : List NatAssign.Instruction :=
  [.add 1250 2606,.copy 2606 571,.literal 2608 1,.add 2608 571,
   .literal 2608 1048576,.multiply 2608 571,.add 990 571,.literal 2608 4179,
   .add 2608 571,.copy 1209 570,.copy 2600 572]
def scanned (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.LengthSum.initializedValues 2606 2607 5 sources (loaded v)
def values (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values plan (scanned v)

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i :=by
  simp only [ids,sources,parameterSources,sourceSources,geometrySources,otherSources,clearHeaders,
    Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

theorem valid : ∀a∈plan,a.Valid ids:=by
  intro a ha
  simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (simp only [NatAssign.Instruction.Valid];decide)

theorem source_valid (i : ℕ) (hi : i∈sources) : i∈ids ∧ i≠2606 ∧ i≠2607:=by
  refine ⟨Finset.mem_union_left _ (by simpa only [List.mem_toFinset] using hi),?_,?_⟩
  all_goals
    simp only [sources,parameterSources,sourceSources,geometrySources,otherSources,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    omega

theorem source_not_header (i : ℕ) (hi : i∈sources) : i∉clearHeaders:=by
  have h : Disjoint sources.toFinset clearHeaders.toFinset:=by decide
  exact fun he=>Finset.disjoint_left.mp h (by simpa only [List.mem_toFinset] using hi)
    (by simpa only [List.mem_toFinset] using he)

theorem loaded_total (v : ℕ→ℕ) : NatAssign.LengthSum.total sources (loaded v)=
    NatAssign.LengthSum.total sources v:=by
  apply NatAssign.LengthSum.total_congr
  intro k hk
  simp only [loaded,ite_eq_right (source_not_header k hk)]

theorem outputs (v : ℕ→ℕ) : values v 2606=budget v ∧ values v 570=v 1209 ∧
    values v 571=slotWidth v ∧ values v 572=v 2600 ∧ values v 573=0:=by
  simp only [values,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,scanned,NatAssign.LengthSum.initializedValues]
  simp [loaded_total,loaded,clearHeaders,budget,slotWidth]
  constructor <;> ring

theorem source_kept (v : ℕ→ℕ) (i : ℕ) (hi : i∈sources) : values v i=v i:=by
  have hn := source_not_header i hi
  have ha : ∀a∈plan,i≠a.target:=by
    intro a ha
    simp only [clearHeaders,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    simp only [plan,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals (simp only [NatAssign.Instruction.target];omega)
  rw [values,NatAssign.values_preserves _ _ i ha]
  have hs:=source_valid i hi
  simp only [scanned,NatAssign.LengthSum.initializedValues,Function.update_of_ne hs.2.1,
    Function.update_of_ne hs.2.2,loaded,ite_eq_right hn]

theorem budget_width (v : ℕ→ℕ) (i : ℕ) (hi : i∈sources) : (v i).bits.length≤budget v:=by
  have h:=NatAssign.LengthSum.member_le_total sources v i hi
  unfold budget
  omega

theorem budget_ge (v : ℕ→ℕ) : 5≤budget v:=by unfold budget;omega
theorem geometry_width (v : ℕ→ℕ) : v 1250≤budget v:=by unfold budget;omega
theorem slot_positive (v : ℕ→ℕ) : 0<slotWidth v:=by unfold slotWidth;omega

#print axioms outputs
end Maxwell.Continuum.WellStrengthInitialization.Table
