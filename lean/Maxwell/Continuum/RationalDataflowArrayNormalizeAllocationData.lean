import Maxwell.Continuum.RationalDataflowArrayNormalizeMachine
import Maxwell.Continuum.CalibrationNormalizationAllocation
import Maxwell.Cost.Structured.NatAssign.LengthSum

/-! Runtime allocation for array normalization. The storage request is
computed from measured operands, the actual input width, count and precision. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
open Maxwell.Cost Maxwell.Cost.Structured Calibration
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def sourceIds : Finset ℕ := RationalRoot.Stored.ids 24∪RationalDataflow.ports slots∪{200,202,203,204,788}
def sources : List ℕ := sourceIds.sort (·≤·)
def workIds : Finset ℕ := {201,787,570,571,572,573,574,802,803,804,805}
def allIds : Finset ℕ := sourceIds∪workIds
def budget (n : ℕ→ℕ) : ℕ := 1000+NatAssign.LengthSum.total sources n+n 200
def measured (n : ℕ→ℕ) := NatAssign.LengthSum.initializedValues 802 803 1000 sources n
def measureCode : Code := NatAssign.LengthSum.initializedCode 802 803 1000 sources
def capacity (n : ℕ→ℕ) : ℕ := 2*Normalize.width (n 788) (n 700) (budget n)+1
def heap (n : ℕ→ℕ) : ℕ := n 202+n 203+n 204+n 788*n 200
def heapEnd (n : ℕ→ℕ) : ℕ := heap n+3*n 788*capacity n
def plan : List NatAssign.Instruction :=
  [.add 200 802,.copy 802 571,.literal 804 1,.add 804 571,
   .copy 788 805,.add 804 805,.multiply 805 571,.literal 804 32,.multiply 804 571,
   .copy 700 805,.literal 804 24,.multiply 804 805,.add 805 571,.literal 804 49,.add 804 571,
   .copy 788 572,.multiply 200 572,.add 202 572,.add 203 572,.add 204 572,
   .copy 788 570,.literal 573 0,.copy 788 201,.copy 788 787,
   .copy 570 574,.multiply 571 574,.literal 804 3,.multiply 804 574,.add 572 574]
def planned (n : ℕ→ℕ) := NatAssign.values plan (measured n)

theorem capacity_eq (n : ℕ→ℕ) : capacity n=32*(n 788+1)*(budget n+1)+24*n 700+49 := by
  unfold capacity Normalize.width RationalRoot.normalizeScalarWidth RationalRoot.outputWidth
    squaresWidth sumWidth
  ring
theorem capacity_pos (n : ℕ→ℕ) : 0<capacity n := by unfold capacity;omega
theorem allIds_ge (k : ℕ) (hk : k∈allIds) : 4 ≤ k := by
  rcases Finset.mem_union.mp hk with hs|hw
  · rcases Finset.mem_union.mp hs with hs|hh
    · rcases Finset.mem_union.mp hs with hr|hp
      · exact RationalRoot.Stored.ids_ge 24 k hr
      · exact RationalDataflow.ids_ge slots k (Finset.mem_union_left _ hp)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hh;omega
  · simp only [workIds,Finset.mem_insert,Finset.mem_singleton] at hw;omega
theorem source_external (k : ℕ) (hk : k∈sourceIds) : k≠802 ∧ k≠803 := by
  have h : Disjoint sourceIds ({802,803}:Finset ℕ) := by decide
  exact ⟨fun he=>Finset.disjoint_left.mp h hk (by simp [he]),
    fun he=>Finset.disjoint_left.mp h hk (by simp [he])⟩
theorem sources_valid : ∀k∈sources,k∈allIds ∧ k≠802 ∧ k≠803 := by
  intro k hk
  have hs:k∈sourceIds:=by simpa only [sources,Finset.mem_sort] using hk
  exact ⟨Finset.mem_union_left _ hs,source_external k hs⟩
theorem measured_source (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : measured n k=n k := by
  simp only [measured,NatAssign.LengthSum.initializedValues,
    Function.update_of_ne (source_external k hk).1,Function.update_of_ne (source_external k hk).2]
theorem budget_bound (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : (n k).bits.length≤budget n := by
  have h:=NatAssign.LengthSum.member_le_total sources n k (by simpa only [sources,Finset.mem_sort] using hk)
  unfold budget
  omega
theorem budget_ge (n : ℕ→ℕ) : 1000≤budget n := by unfold budget;omega
theorem budget_table (n : ℕ→ℕ) : n 200≤budget n := by unfold budget;omega
theorem plan_valid : ∀a∈plan,a.Valid allIds := by
  simp [plan,NatAssign.Instruction.Valid,allIds,sourceIds,workIds,RationalRoot.Stored.ids]
theorem plan_source (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : planned n k=n k := by
  rw [planned,NatAssign.values_preserves,measured_source n k hk]
  intro a ha he
  have targets : ∀a∈plan,a.target∈workIds := by decide
  have disjoint : Disjoint sourceIds workIds := by decide
  exact Finset.disjoint_left.mp disjoint hk (he ▸ targets a ha)
theorem plan_outputs (n : ℕ→ℕ) :
    planned n 570=n 788 ∧ planned n 571=capacity n ∧ planned n 572=heap n ∧
    planned n 573=0 ∧ planned n 802=budget n ∧ planned n 201=n 788 ∧ planned n 787=n 788 := by
  have h700:=measured_source n 700 (by decide)
  have h788:=measured_source n 788 (by decide)
  have h200:=measured_source n 200 (by decide)
  have h202:=measured_source n 202 (by decide)
  have h203:=measured_source n 203 (by decide)
  have h204:=measured_source n 204 (by decide)
  have h802 : measured n 802=1000+NatAssign.LengthSum.total sources n := rfl
  rw [capacity_eq]
  simp [planned,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,h700,h788,h200,h202,h203,h204,h802,heap,budget]
  and_intros <;> ring

theorem plan_heapEnd (n : ℕ→ℕ) : planned n 574=heapEnd n := by
  have h700:=measured_source n 700 (by decide)
  have h788:=measured_source n 788 (by decide)
  have h200:=measured_source n 200 (by decide)
  have h202:=measured_source n 202 (by decide)
  have h203:=measured_source n 203 (by decide)
  have h204:=measured_source n 204 (by decide)
  have h802 : measured n 802=1000+NatAssign.LengthSum.total sources n := rfl
  simp [planned,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,h700,h788,h200,h202,h203,h204,h802,heapEnd,capacity_eq,heap,budget]
  ring

#print axioms plan_outputs
#print axioms plan_heapEnd
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
