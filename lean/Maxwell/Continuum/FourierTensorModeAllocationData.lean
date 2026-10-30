import Maxwell.Continuum.FourierTensorModeTableCorrect
import Maxwell.Continuum.ProfileCacheAllocation
import Maxwell.Continuum.StoredWordLength

/-! Actual row-buffer dimensions are computed from stored mode parameters.
The slot width uses scanned input lengths; the heap lies beyond every
channel of the calibration array. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def inputs : Finset ℕ := {200,202,203,204,350,352,354,355}
def ids : Finset ℕ := inputs∪ModeIndex.ports∪{145,201,353,356,357,358,360,361,362,725,726,727,728}
def changed : Finset ℕ := {0,1,2,3}∪ids
def initial (M L R P width bp bn bd : ℕ) (i : ℕ) : ℕ :=
  if i=200 then width else if i=202 then bp else if i=203 then bn else if i=204 then bd else
  if i=350 then M else if i=352 then L else if i=354 then R else if i=355 then P else 0
def scanned (M L R P width bp bn bd : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update (initial M L R P width bp bn bd)
    360 M.bits.length) 361 L.bits.length) 362 R.bits.length
def scanCode : Code := .seq (WordLength.code 350 360)
  (.seq (WordLength.code 352 361) (WordLength.code 354 362))
def instructions : List NatAssign.Instruction :=
  [.copy 354 311,.copy 354 356,.literal 353 2,.multiply 353 356,
   .literal 353 1,.add 353 356,.copy 356 357,.multiply 356 357,
   .copy 357 358,.multiply 356 358,.copy 358 201,
   .copy 358 322,.literal 353 3,.multiply 353 322,
   .copy 358 725,.literal 353 5,.multiply 353 725,.copy 355 145,
   .copy 322 727,.literal 353 2,.multiply 353 727,.multiply 200 727,
   .add 202 727,.add 203 727,.add 204 727,
   .copy 355 726,.add 360 726,.add 361 726,.add 362 726,
   .literal 353 16,.add 353 726,.literal 353 0]
def values (M L R P width bp bn bd : ℕ) : ℕ→ℕ :=
  NatAssign.values instructions (scanned M L R P width bp bn bd)
def code : Code := .seq scanCode (NatAssign.code instructions)
def slotWidth (M L R P : ℕ) : ℕ := P+M.bits.length+L.bits.length+R.bits.length+16
def heap (R width bp bn bd : ℕ) : ℕ := bp+bn+bd+2*aliasArraySize R*width

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,inputs,ModeIndex.ports,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem instructions_valid : ∀a∈instructions,a.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids,inputs,ModeIndex.ports]

theorem values_rowCount (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 201=RowArithmetic.rowCount R := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,RowArithmetic.rowCount,aliasSide]
  ring

theorem values_size (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 322=aliasArraySize R := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,aliasArraySize,aliasSide]
  ring

theorem values_length (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 725=5*RowArithmetic.rowCount R := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,RowArithmetic.rowCount,aliasSide]
  ring

theorem values_width (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 726=slotWidth M L R P := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,slotWidth]
  omega

theorem values_heap (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 727=heap R width bp bn bd := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,heap,aliasArraySize,aliasSide]
  ring

theorem values_precision (M L R P width bp bn bd : ℕ) :
    values M L R P width bp bn bd 145=P := by
  simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem values_modeIndex (M L R P width bp bn bd i : ℕ) (hi : i∈ModeIndex.ports) :
    values M L R P width bp bn bd i=ModeIndex.initial R (aliasArraySize R) 0 i := by
  by_cases h311 : i=311
  · subst i
    simp [values,instructions,scanned,initial,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,ModeIndex.initial]
  by_cases h322 : i=322
  · subst i
    rw [values_size]
    simp [ModeIndex.initial]
  have bounds := Finset.mem_Icc.mp hi
  have hx : values M L R P width bp bn bd i=scanned M L R P width bp bn bd i := by
    exact values_unchanged instructions _ i (by
      simp only [instructions,List.mem_cons,List.not_mem_nil,or_false]
      intro a ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [NatAssign.Instruction.target] <;> omega)
  rw [hx]
  simp (disch := omega) [scanned,initial,ModeIndex.initial,h311,h322]
  split_ifs <;> omega

theorem slotWidth_pos (M L R P : ℕ) : 0<slotWidth M L R P := by unfold slotWidth;omega

theorem input_separated (M L R P : ℕ) (a : Table (2*aliasArraySize R)) (memory : ℕ→Bool) :
    a.SeparatedFrom (Profile.Runtime.memoryTable (5*RowArithmetic.rowCount R) (slotWidth M L R P)
      (heap R (addressValue a.width) (addressValue a.basePositive)
        (addressValue a.baseNegative) (addressValue a.baseDenominator)) (slotWidth_pos M L R P) memory) := by
  intro x hx y hy
  simp only [Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl|rfl
  all_goals
    simp only [Profile.Runtime.memoryTable,addressValue_bits,IncidenceEncoding.Separated]
    left
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> unfold heap <;> omega

#print axioms values_modeIndex
#print axioms input_separated
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
