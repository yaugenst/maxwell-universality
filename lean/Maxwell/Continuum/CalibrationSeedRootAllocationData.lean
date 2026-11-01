import Maxwell.Continuum.CalibrationSeedRootStorageWidth
import Maxwell.Continuum.CalibrationNormalizationAllocation
import Maxwell.Cost.Structured.NatAssign.LengthSum

/-! The seed destination width is selected from actual word lengths and the
cached coefficient width. Its heap starts after the cache's last channel. -/
namespace Maxwell.Continuum.Calibration.SeedRoot.Allocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def sourceIds : Finset ℕ := rowIds∪RationalDataflow.ports slots∪{200,202,203,204,801}
def sources : List ℕ := sourceIds.sort (·≤·)
def workIds : Finset ℕ := {570,571,572,573,802,803,804,805,806,807,808}
def allIds : Finset ℕ := sourceIds∪workIds
def budget (n : ℕ→ℕ) : ℕ := 1000+NatAssign.LengthSum.total sources n+n 200
def measured (n : ℕ→ℕ) := NatAssign.LengthSum.initializedValues 802 803 1000 sources n
def measureCode : Code := NatAssign.LengthSum.initializedCode 802 803 1000 sources
def heap (n : ℕ→ℕ) : ℕ := n 202+n 203+n 204+2*(2*n 751+1)^3*n 200
def plan : List NatAssign.Instruction :=
  [.literal 804 2,.copy 751 805,.multiply 804 805,.literal 806 1,.add 806 805,
   .copy 805 806,.multiply 805 806,.multiply 805 806,.multiply 804 806,
   .copy 806 572,.multiply 200 572,.add 204 572,.add 202 572,.add 203 572,.copy 788 570,
   .add 200 802,.copy 802 571,.literal 804 (2^321),.multiply 804 571,
   .literal 804 (producerWidth 0),.add 804 571,.literal 573 0]
def planned (n : ℕ→ℕ) := NatAssign.values plan (measured n)

theorem allIds_ge (k : ℕ) (hk : k∈allIds) : 4≤k := by
  rcases Finset.mem_union.mp hk with hs|hw
  · rcases Finset.mem_union.mp hs with hs|hh
    · rcases Finset.mem_union.mp hs with hr|hp
      · exact (by decide : 4≤10).trans (rowIds_lower k hr)
      · have hi : k∈RationalDataflow.ids slots := Finset.mem_union_left _ hp
        exact RationalDataflow.ids_ge slots k hi
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
theorem budget_cache (n : ℕ→ℕ) : n 200≤budget n := by unfold budget;omega
theorem plan_valid : ∀a∈plan,a.Valid allIds := by
  simp [plan,NatAssign.Instruction.Valid,allIds,sourceIds,workIds,rowIds,ids,extra,
    SelectedParameters.Compare.ids]
theorem plan_source (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : planned n k=n k := by
  rw [planned,NatAssign.values_preserves,measured_source n k hk]
  intro a ha he
  have targets : ∀a∈plan,a.target∈workIds := by decide
  have disjoint : Disjoint sourceIds workIds := by decide
  exact Finset.disjoint_left.mp disjoint hk (he ▸ targets a ha)
theorem plan_outputs (n : ℕ→ℕ) :
    planned n 570=n 788 ∧ planned n 571=producerWidth (budget n) ∧
    planned n 572=heap n ∧ planned n 573=0 ∧ planned n 802=budget n := by
  have h751:=measured_source n 751 (by decide)
  have h788:=measured_source n 788 (by decide)
  have h200:=measured_source n 200 (by decide)
  have h202:=measured_source n 202 (by decide)
  have h203:=measured_source n 203 (by decide)
  have h204:=measured_source n 204 (by decide)
  have h802 : measured n 802=1000+NatAssign.LengthSum.total sources n := rfl
  rw [producerWidth_affine (budget n)]
  simp [planned,plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,h751,h788,h200,h202,h203,h204,h802,heap,budget]
  and_intros <;> ring

#print axioms plan_outputs
end Maxwell.Continuum.Calibration.SeedRoot.Allocation
