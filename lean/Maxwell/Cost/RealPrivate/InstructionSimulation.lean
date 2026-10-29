import Maxwell.Cost.RealPrivate.BasicInstructions
import Maxwell.Cost.RealPrivate.InputInstructions
import Maxwell.Cost.RealPrivate.MemoryInstructions
import Maxwell.Cost.RealPrivate.OutputInstructions

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def writeAddress (op : RAMInstruction) (s : RAMState) : Option ℕ :=
  match op with
  | .literal dst _ | .copy dst _ | .add dst _ _ | .multiply dst _ _ | .divide dst _ _ |
      .input dst _ | .inputIndex dst _ | .load dst _ | .loadIndex dst _ |
      .indexLiteral dst _ | .indexCopy dst _ | .indexAdd dst _ _ | .indexSubtract dst _ _ |
      .randomBit dst => some dst
  | .store address _ | .storeIndex address _ => some (s.indices address)
  | _ => none

def recorded (op : RAMInstruction) (source : RAMState) (written : List ℕ) : List ℕ :=
  match writeAddress op source with
  | none => written
  | some address => address :: written

theorem recorded_length_le (op : RAMInstruction) (source : RAMState) (written : List ℕ) :
    (recorded op source written).length ≤ written.length + 1 := by
  unfold recorded
  split <;> simp

def instructionBound (L : Layout) : ℕ := 2 * L.realInputStride + 2 * L.indexInputStride + 50

theorem Covered.next {M : Machine} {sourceInput : RAMInput} {tape : ℕ → Bool}
    {source next : RAMState} {written : List ℕ} (h : Covered source written)
    (op : RAMInstruction) (hcode : M.code[source.pc]? = some op)
    (hnext : M.next sourceInput tape source = some next) :
    Covered next (recorded op source written) := by
  cases op <;> simp only [Machine.next, hcode, Option.some.injEq, reduceCtorEq] at hnext
  all_goals subst next
  all_goals first | exact h.private_word _ _ | exact h.private_index _ _ | exact h

/-- Every successful source transition is executed by its finite literal
translation, with no restrictions on the source's indirect addresses. -/
theorem instruction_next (M : Machine) (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source next : RAMState} {written : List ℕ}
    (op : RAMInstruction) (hcode : M.code[source.pc]? = some op)
    (hnext : M.next sourceInput tape source = some next)
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) :
    ∃ cost t, cost ≤ instructionBound L ∧
      Executes externalInput tape (instruction L op) cost s t ∧
      Represents origin next (recorded op source written) t.val ∧ CallerFrame origin s.val t.val := by
  cases op <;> simp only [Machine.next, hcode, Option.some.injEq, reduceCtorEq] at hnext
  all_goals subst next
  case literal dst q =>
    obtain ⟨t, he, ht, hf⟩ := literal_instruction externalInput tape s h dst q
    exact ⟨29, t, by unfold instructionBound; omega, he, ht, hf⟩
  case copy dst src =>
    obtain ⟨t, he, ht, hf⟩ := copy_instruction externalInput tape s h dst src
    exact ⟨33, t, by unfold instructionBound; omega, he, ht, hf⟩
  case add dst left right =>
    obtain ⟨t, he, ht, hf⟩ := binary_word_instruction externalInput tape s h dst left right
      (realAdd 2 0 1) (· + ·) (fun v => realAdd_executes externalInput tape v 2 0 1)
    exact ⟨41, t, by unfold instructionBound; omega, he, ht, hf⟩
  case multiply dst left right =>
    obtain ⟨t, he, ht, hf⟩ := binary_word_instruction externalInput tape s h dst left right
      (realMultiply 2 0 1) (· * ·) (fun v => realMultiply_executes externalInput tape v 2 0 1)
    exact ⟨41, t, by unfold instructionBound; omega, he, ht, hf⟩
  case divide dst left right =>
    obtain ⟨t, he, ht, hf⟩ := binary_word_instruction externalInput tape s h dst left right
      (realDivide 2 0 1) (· / ·) (fun v => realDivide_executes externalInput tape v 2 0 1)
    exact ⟨41, t, by unfold instructionBound; omega, he, ht, hf⟩
  case input dst address =>
    obtain ⟨cost, t, hc, he, ht, hf⟩ := input_instruction externalInput sourceInput tape s h hi dst address
    exact ⟨cost, t, by unfold instructionBound; omega, he, ht, hf⟩
  case inputIndex dst address =>
    obtain ⟨cost, t, hc, he, ht, hf⟩ := inputIndex_instruction externalInput sourceInput tape s h hi dst address
    exact ⟨cost, t, by unfold instructionBound; omega, he, ht, hf⟩
  case load dst address =>
    obtain ⟨t, he, ht, hf⟩ := load_instruction externalInput tape s h dst address
    exact ⟨48, t, by unfold instructionBound; omega, he, ht, hf⟩
  case store address src =>
    obtain ⟨t, he, ht, hf⟩ := store_instruction externalInput tape s h address src
    exact ⟨46, t, by unfold instructionBound; omega, he, ht, hf⟩
  case loadIndex dst address =>
    obtain ⟨t, he, ht, hf⟩ := loadIndex_instruction externalInput tape s h dst address
    exact ⟨48, t, by unfold instructionBound; omega, he, ht, hf⟩
  case storeIndex address src =>
    obtain ⟨t, he, ht, hf⟩ := storeIndex_instruction externalInput tape s h address src
    exact ⟨46, t, by unfold instructionBound; omega, he, ht, hf⟩
  case indexLiteral dst value =>
    obtain ⟨t, he, ht, hf⟩ := indexLiteral_instruction externalInput tape s h dst value
    exact ⟨29, t, by unfold instructionBound; omega, he, ht, hf⟩
  case indexCopy dst src =>
    obtain ⟨t, he, ht, hf⟩ := indexCopy_instruction externalInput tape s h dst src
    exact ⟨33, t, by unfold instructionBound; omega, he, ht, hf⟩
  case indexAdd dst left right =>
    obtain ⟨t, he, ht, hf⟩ := binary_index_instruction externalInput tape s h dst left right
      (add valueRegister leftRegister rightRegister) (· + ·)
      (fun v => add_executes externalInput tape v valueRegister leftRegister rightRegister)
    exact ⟨41, t, by unfold instructionBound; omega, he, ht, hf⟩
  case indexSubtract dst left right =>
    obtain ⟨t, he, ht, hf⟩ := binary_index_instruction externalInput tape s h dst left right
      (subtract valueRegister leftRegister rightRegister) (· - ·)
      (fun v => subtract_executes externalInput tape v valueRegister leftRegister rightRegister)
    exact ⟨41, t, by unfold instructionBound; omega, he, ht, hf⟩
  case branchLE left right yes no =>
    obtain ⟨t, he, ht, hf⟩ := branch_real_instruction externalInput tape s h left right yes no
    exact ⟨16, t, by unfold instructionBound; omega, he, ht, hf⟩
  case branchIndexLE left right yes no =>
    obtain ⟨t, he, ht, hf⟩ := branch_index_instruction externalInput tape s h left right yes no
    exact ⟨15, t, by unfold instructionBound; omega, he, ht, hf⟩
  case jump pc =>
    obtain ⟨t, he, ht, hf⟩ := jump_instruction externalInput tape s h pc
    exact ⟨2, t, by unfold instructionBound; omega, he, ht, hf⟩
  case randomBit dst =>
    obtain ⟨t, he, ht, hf⟩ := random_instruction externalInput tape s h dst
    exact ⟨29, t, by unfold instructionBound; omega, he, ht, hf⟩
  case output src =>
    obtain ⟨t, he, ht, hf⟩ := output_instruction externalInput tape s h src
    exact ⟨25, t, by unfold instructionBound; omega, he, ht, hf⟩
  case outputIndex src =>
    obtain ⟨t, he, ht, hf⟩ := outputIndex_instruction externalInput tape s h src
    exact ⟨25, t, by unfold instructionBound; omega, he, ht, hf⟩

end Maxwell.Cost.RealPrivate
