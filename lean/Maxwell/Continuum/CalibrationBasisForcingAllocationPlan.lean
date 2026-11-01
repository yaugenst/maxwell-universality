import Maxwell.Continuum.CalibrationBasisForcingGenerated
import Maxwell.Continuum.CalibrationNormalizationAllocation

/-! A concrete source table has three625-bit slots per entry. Its count is
computed from the radius; only the free heap address is read from word376. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank

def allocationIds : Finset ℕ := naturalIds∪{376,570,571,572,573}
def allocationPlan : List NatAssign.Instruction := counterPlan++
  [.copy 315 570,.literal 571 625,.copy 376 572,.literal 573 0]
def allocationValues (n : ℕ → ℕ) : ℕ → ℕ := NatAssign.values allocationPlan n
def allocationWidth (B : ℕ) : ℕ := 2^13*(B+1)
def metadataWidth (B : ℕ) : ℕ := 2*allocationWidth B+1000

theorem allocationIds_ge (k : ℕ) (hk : k∈allocationIds) : 10≤k := by
  rcases Finset.mem_union.mp hk with hn|hn
  · exact naturalIds_ge k hn
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    omega

theorem allocation_valid : ∀a∈allocationPlan,a.Valid allocationIds := by
  have h311 : 311∈allocationIds := Finset.mem_union_left _ (naturalIds_decode (by decide))
  have h312 : 312∈allocationIds := Finset.mem_union_left _ (naturalIds_decode (by decide))
  have h313 : 313∈allocationIds := Finset.mem_union_left _ (naturalIds_decode (by decide))
  have h314 : 314∈allocationIds := Finset.mem_union_left _ (naturalIds_decode (by decide))
  have h315 : 315∈allocationIds := Finset.mem_union_left _ (naturalIds_decode (by decide))
  have extra (k : ℕ) (hk : k∈({376,570,571,572,573}:Finset ℕ)) : k∈allocationIds := Finset.mem_union_right _ hk
  simp [allocationPlan,counterPlan,prepare,NatAssign.Instruction.Valid,h311,h312,h313,h314,h315,
    extra 376 (by decide),extra 570 (by decide),extra 571 (by decide),extra 572 (by decide),extra 573 (by decide)]

theorem allocation_outputs (n : ℕ → ℕ) :
    allocationValues n 315=aliasArraySize (n 311) ∧ allocationValues n 570=aliasArraySize (n 311) ∧
    allocationValues n 571=625 ∧ allocationValues n 572=n 376 ∧ allocationValues n 573=0 := by
  simp [allocationValues,allocationPlan,counterPlan,prepare,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,aliasArraySize,aliasSide]
  ring

theorem allocationValues_keep (n : ℕ → ℕ) (k : ℕ)
    (hk : k≠312 ∧ k≠313 ∧ k≠314 ∧ k≠315 ∧ k≠570 ∧ k≠571 ∧ k≠572 ∧ k≠573) :
    allocationValues n k=n k := by
  apply values_unchanged
  simp [allocationPlan,counterPlan,prepare,NatAssign.Instruction.target,
    Ne.symm hk.1,Ne.symm hk.2.1,Ne.symm hk.2.2.1,Ne.symm hk.2.2.2.1,
    Ne.symm hk.2.2.2.2.1,Ne.symm hk.2.2.2.2.2.1,Ne.symm hk.2.2.2.2.2.2.1,Ne.symm hk.2.2.2.2.2.2.2]

theorem allocation_agrees (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (k : ℕ) (hk : k∈ids bank) :
    allocationValues n k=dataValues v k := by
  have neq (i : ℕ) (hi : i<1000) (hw : i∉workPorts) : k≠i := fun he =>
    outside_bank i hi hw (he ▸ hk)
  rw [allocationValues_keep n k ⟨neq _ (by decide) (by decide),neq _ (by decide) (by decide),
    neq _ (by decide) (by decide),neq _ (by decide) (by decide),neq _ (by decide) (by decide),
    neq _ (by decide) (by decide),neq _ (by decide) (by decide),neq _ (by decide) (by decide)⟩,
    agree k hk]

theorem allocation_literals (B : ℕ) (hB : 103≤B) : ∀a∈allocationPlan,a.literalWidth≤B := by
  simp [allocationPlan,counterPlan,prepare,NatAssign.Instruction.literalWidth,
    show (3:ℕ).bits.length=2 by decide,show (625:ℕ).bits.length=10 by decide]
  omega

theorem allocation_width (n : ℕ → ℕ) (B : ℕ) (hB : 103≤B)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B) :
    ∀k∈allocationIds,(allocationValues n k).bits.length≤allocationWidth B := by
  have h := NatAssign.values_width_bound allocationIds allocationPlan allocation_valid n B hw (allocation_literals B hB)
  intro k hk
  have hh := h k hk
  change (allocationValues n k).bits.length+1≤2^13*(B+1) at hh
  unfold allocationWidth
  omega

theorem natural_outside (k : ℕ) (hk : k<1000) (hwork : k∉workPorts)
    (hdecode : k∉ArrayDecodeMachine.ports) (hdiv : k∉NaturalQuotient.workPorts) : k∉naturalIds := by
  simp only [naturalIds,Finset.mem_union,not_or]
  exact ⟨⟨outside_bank k hk hwork,hdecode⟩,hdiv⟩

theorem allocation_stage_external (k : ℕ)
    (hk : k∈([5,6,7,8,9,37,201,210,212,213,214,215,216]:List ℕ)) :
    k∉({0,1,2,3,4}∪allocationIds:Finset ℕ) := by
  have bounds : 5≤k ∧ k<1000 ∧ k∉workPorts ∧ k∉ArrayDecodeMachine.ports ∧
      k∉NaturalQuotient.workPorts ∧ k≠376 ∧ k≠570 ∧ k≠571 ∧ k≠572 ∧ k≠573 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [allocationIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨by omega,natural_outside k bounds.2.1 bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.1,
    bounds.2.2.2.2.2⟩

theorem allocation_preserves_natural (k : ℕ) (hk : k∈naturalIds) :
    k∉PowerMachine.BufferNorm.Allocation.changed := by
  intro hh
  simp only [PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact natural_outside _ (by decide) (by decide) (by decide) (by decide) hk

def workWidth (B : ℕ) : ℕ := 2^8*(allocationWidth B+1)

theorem allocation_work_width (n : ℕ→ℕ) (B : ℕ) (hB : 103≤B)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B) :
    ∀k∈PowerMachine.BufferNorm.Allocation.inputs,
      (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n) k).bits.length≤workWidth B := by
  have inputWidth : ∀k∈PowerMachine.BufferNorm.Allocation.inputs,
      (allocationValues n k).bits.length≤allocationWidth B := by
    intro k hk
    apply allocation_width n B hB hw k
    apply Finset.mem_union_right
    simp only [PowerMachine.BufferNorm.Allocation.inputs,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto
  have widths:=NatAssign.values_width_bound PowerMachine.BufferNorm.Allocation.ids
    PowerMachine.BufferNorm.Allocation.plan PowerMachine.BufferNorm.Allocation.valid
    (PowerMachine.BufferNorm.Allocation.clearedValues (allocationValues n)) (allocationWidth B)
    (PowerMachine.BufferNorm.Allocation.cleared_width _ _ inputWidth)
    (by simp [PowerMachine.BufferNorm.Allocation.plan,NatAssign.Instruction.literalWidth])
  intro k hk
  have h:=widths k (Finset.mem_union_left _ hk)
  change (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n) k).bits.length+1≤
    2^8*(allocationWidth B+1) at h
  unfold workWidth
  omega

#print axioms allocation_outputs
end Maxwell.Continuum.Calibration.BasisForcing
