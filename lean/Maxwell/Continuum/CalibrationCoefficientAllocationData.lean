import Maxwell.Continuum.CalibrationGeneratedInverse
import Maxwell.Continuum.CalibrationNormalizationAllocation
import Maxwell.Cost.Structured.NatAssign.LengthSum
import Maxwell.Cost.Structured.NatAssign.Values

/-! The coefficient destination is selected from a measured budget and the
actual source-array headers. Its heap begins after the source denominator
channel; its width is exactly the established coefficient-generation bound. -/
namespace Maxwell.Continuum.Calibration.CoefficientAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def sourceIds : Finset ℕ := emissionIds∪{200,202,203,204}
def sources : List ℕ := sourceIds.sort (·≤·)
def workIds : Finset ℕ := {570,571,572,573,580,581,582,583,584}
def allIds : Finset ℕ := sourceIds∪workIds
def budget (n : ℕ→ℕ) : ℕ := 626+NatAssign.LengthSum.total sources n
def measured (n : ℕ→ℕ) : ℕ→ℕ := NatAssign.LengthSum.initializedValues 580 581 626 sources n
def measureCode : Code := NatAssign.LengthSum.initializedCode 580 581 626 sources

def slotOffset : ℕ := coefficientWidth (countWidth 0)
def slotWidth (B : ℕ) : ℕ := 2^717*B+slotOffset

theorem slotWidth_eq (B : ℕ) : slotWidth B=coefficientWidth (countWidth B) := by
  unfold slotWidth slotOffset coefficientWidth coefficientBaseWidth countWidth
    forcingEmissionWidth forcingBaseWidth RawFree.forcingVectorWidth emissionWidth
    emissionBaseWidth matrixEntryWordBound RawFree.matrixEntryWidth
  ring

theorem slotWidth_pos (B : ℕ) : 0<slotWidth B := by
  rw [slotWidth_eq]
  unfold coefficientWidth emissionWidth matrixEntryWordBound RawFree.matrixEntryWidth
  positivity

def plan : List NatAssign.Instruction :=
  [.literal 582 2,.multiply 311 582,.literal 583 1,.add 583 582,
   .copy 582 583,.multiply 582 583,.multiply 582 583,.literal 584 3,.multiply 584 583,
   .copy 583 570,.multiply 583 570,.add 583 570,.add 583 570,
   .copy 583 572,.multiply 200 572,.add 204 572,
   .copy 580 571,.literal 584 (2^717),.multiply 584 571,.literal 584 slotOffset,.add 584 571,
   .literal 573 0]
def planned (n : ℕ→ℕ) : ℕ→ℕ := NatAssign.values plan (measured n)
def heap (n : ℕ→ℕ) : ℕ := n 204+aliasArraySize (n 311)*n 200

theorem allIds_ge (k : ℕ) (hk : k∈allIds) : 4≤k := by
  rcases Finset.mem_union.mp hk with hs|hw
  · rcases Finset.mem_union.mp hs with hs|hh
    · exact (emissionIds_ge k hs).trans' (by decide)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hh;omega
  · simp only [workIds,Finset.mem_insert,Finset.mem_singleton] at hw;omega

theorem source_external (k : ℕ) (hk : k∈sourceIds) : k≠580 ∧ k≠581 := by
  have h : Disjoint sourceIds ({580,581}:Finset ℕ) := by decide
  exact ⟨fun he=>Finset.disjoint_left.mp h hk (by simp [he]),
    fun he=>Finset.disjoint_left.mp h hk (by simp [he])⟩

theorem sources_valid : ∀k∈sources,k∈allIds ∧ k≠580 ∧ k≠581 := by
  intro k hk
  have hs:k∈sourceIds:=by simpa only [sources,Finset.mem_sort] using hk
  exact ⟨Finset.mem_union_left _ hs,source_external k hs⟩

theorem measured_source (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : measured n k=n k := by
  simp only [measured,NatAssign.LengthSum.initializedValues,
    Function.update_of_ne (source_external k hk).1,Function.update_of_ne (source_external k hk).2]

theorem measured_budget (n : ℕ→ℕ) : measured n 580=budget n := rfl

theorem budget_bound (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : (n k).bits.length≤budget n :=
  (NatAssign.LengthSum.member_le_total sources n k (by simpa only [sources,Finset.mem_sort] using hk)).trans
    (Nat.le_add_left _ _)

theorem budget_ge (n : ℕ→ℕ) : 626≤budget n := Nat.le_add_right _ _

theorem plan_valid : ∀a∈plan,a.Valid allIds := by
  simp [plan,NatAssign.Instruction.Valid,allIds,sourceIds,workIds,emissionIds]

theorem plan_source (n : ℕ→ℕ) (k : ℕ) (hk : k∈sourceIds) : planned n k=n k := by
  rw [planned,NatAssign.values_preserves,measured_source n k hk]
  intro a ha he
  have targets : ∀a∈plan,a.target∈({570,571,572,573,582,583,584}:Finset ℕ) := by decide
  have disjoint : Disjoint sourceIds ({570,571,572,573,582,583,584}:Finset ℕ) := by decide
  exact Finset.disjoint_left.mp disjoint hk (he ▸ targets a ha)

theorem plan_outputs (n : ℕ→ℕ) :
    planned n 570=tableSize (aliasArraySize (n 311)) ∧
    planned n 571=slotWidth (budget n) ∧ planned n 572=heap n ∧ planned n 573=0 := by
  have h311:=measured_source n 311 (by decide)
  have h200:=measured_source n 200 (by decide)
  have h204:=measured_source n 204 (by decide)
  simp only [planned,plan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_self,
    Function.update_of_ne (by decide : (311:ℕ)≠582)]
  simp [h311,h200,h204,measured_budget,heap,slotWidth,aliasArraySize,aliasSide,tableSize]
  constructor
  · ring
  · constructor <;> ring

#print axioms plan_outputs
#print axioms slotWidth_eq
end Maxwell.Continuum.Calibration.CoefficientAllocation
