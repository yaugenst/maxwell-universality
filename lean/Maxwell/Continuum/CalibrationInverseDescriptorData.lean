import Maxwell.Continuum.CalibrationGeneratedInverse
import Maxwell.Cost.Structured.NatAssign.LengthSum

/-! The shared-denominator inverse descriptors are computed from the allocated
raw coefficient table. A measured input budget determines a sufficiently wide
destination; no destination width or address is an oracle input. -/
namespace Maxwell.Continuum.Calibration.InverseDescriptor
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def sourceIds : Finset ℕ := Finset.Icc 107 140∪Finset.Icc 300 309∪
  {210,212,213,214,311,570,571,572,304,580,532,533,534}
def ids : Finset ℕ := sourceIds∪{530,531}
def sources : List ℕ := sourceIds.sort (·≤·)
def budget (v : ℕ→ℕ) : ℕ := 1024+NatAssign.LengthSum.total sources v
def measured (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.LengthSum.initializedValues 530 531 1024 sources v
def measureCode : Code := NatAssign.LengthSum.initializedCode 530 531 1024 sources
def dimension (v : ℕ→ℕ) : ℕ := aliasArraySize (v 311)
def rawWidth (v : ℕ→ℕ) : ℕ := v 571+budget v+1
def heap (v : ℕ→ℕ) : ℕ := v 572+3*v 570*v 571
def bankWidth (v : ℕ→ℕ) : ℕ := 2^80*(budget v+1)*(v 570+2)*(rawWidth v+2)
def slotWidth (v : ℕ→ℕ) : ℕ :=
  2^140*(dimension v+1)^2*(v 304+2)*(rawWidth v+2)*(budget v+1)*(v 570+2)

def plan : List NatAssign.Instruction :=
  [.literal 532 2,.multiply 311 532,.literal 533 1,.add 533 532,
   .copy 532 300,.multiply 532 300,.multiply 532 300,.literal 533 3,.multiply 533 300,
   .copy 570 302,.multiply 571 302,.multiply 533 302,.add 572 302,
   .copy 571 534,.add 530 534,.literal 533 1,.add 533 534,
   .copy 300 301,.add 533 301,.copy 301 532,.multiply 532 301,
   .copy 304 532,.literal 533 2,.add 533 532,.multiply 532 301,
   .copy 534 532,.add 533 532,.multiply 532 301,
   .copy 530 532,.literal 533 1,.add 533 532,.multiply 532 301,
   .copy 570 532,.literal 533 2,.add 533 532,.multiply 532 301,
   .literal 533 (2^140),.multiply 533 301,
   .literal 303 0,.literal 305 0,.literal 306 0,.literal 307 0,.literal 308 0,.literal 309 0]
def values (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values plan (measured v)
def code : Code := .seq measureCode (NatAssign.code plan)

theorem ids_ge (k : ℕ) (hk:k∈ids) : 4≤k := by
  simp only [ids,sourceIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
  omega
theorem sources_valid : ∀k∈sources,k∈ids ∧ k≠530 ∧ k≠531 := by
  intro k hk
  have hs:k∈sourceIds:=by simpa only [sources,Finset.mem_sort] using hk
  refine ⟨Finset.mem_union_left _ hs,?_,?_⟩
  all_goals
    simp only [sourceIds,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hs
    omega
theorem measured_source (v : ℕ→ℕ) (k : ℕ) (hk:k∈sourceIds) : measured v k=v k := by
  have h:=sources_valid k (by simpa only [sources,Finset.mem_sort] using hk)
  simp only [measured,NatAssign.LengthSum.initializedValues,Function.update_of_ne h.2.1,
    Function.update_of_ne h.2.2]
theorem measured_budget (v : ℕ→ℕ) : measured v 530=budget v := rfl
theorem budget_bound (v : ℕ→ℕ) (k : ℕ) (hk:k∈sourceIds) : (v k).bits.length≤budget v :=
  (NatAssign.LengthSum.member_le_total sources v k (by simpa only [sources,Finset.mem_sort] using hk)).trans
    (Nat.le_add_left _ _)
theorem budget_ge (v : ℕ→ℕ) : 1024≤budget v := Nat.le_add_right _ _
theorem plan_valid : ∀a∈plan,a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,sourceIds]

theorem outputs (v : ℕ→ℕ) : values v 300=dimension v ∧ values v 301=slotWidth v ∧
    values v 302=heap v ∧ values v 304=v 304 ∧ values v 534=rawWidth v := by
  have h311:=measured_source v 311 (by decide)
  have h570:=measured_source v 570 (by decide)
  have h571:=measured_source v 571 (by decide)
  have h572:=measured_source v 572 (by decide)
  have h577:=measured_source v 304 (by decide)
  simp only [values,plan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  simp only [Function.update_self,Function.update_of_ne (by decide : (311:ℕ)≠532)]
  simp [h311,h570,h571,h572,h577,measured_budget,dimension,aliasArraySize,aliasSide,slotWidth,heap,rawWidth]
  constructor
  · ring
  · constructor
    · ring
    · constructor
      · ring
      · ring

#print axioms outputs
end Maxwell.Continuum.Calibration.InverseDescriptor
