import Maxwell.Cost.RealSimulation.BooleanInstructions
import Maxwell.Cost.RealSimulation.InputInstructions
import Maxwell.Cost.RealSimulation.OutputInstructions
import Maxwell.Cost.RealSimulation.StackInstructions
import Maxwell.Cost.RealSimulation.TapeInstructions
import Maxwell.Cost.RealSimulation.Footprint

namespace Maxwell.Cost.RealSimulation

open Control

def instructionConstant (L : Layout) : ℕ := 2 * L.stride + 40

/-- Every successful priced source step has an execution of its literal
finite translation. The proof discharges all instruction families, including
aliasing tape reads, random bits, and the charged address-decoding loops. -/
theorem instruction_next (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source next : BitRAMState} {extra : ℕ} (op : BitRAMInstruction)
    (hcode : M.code[source.pc]? = some op) (hfit : Fits L op)
    (hnext : M.next bits tape source = some ⟨next, extra⟩)
    (s : Store) (h : Ready L origin center bits source s)
    (hinput : -(center : ℤ) < source.inputHead)
    (htapes : ∀ t < L.tapeCount, -(center : ℤ) < (source.tapes t).head) :
    ∃ cost t, cost ≤ instructionConstant L * (extra + 1) ∧
      Executes input tape (instruction L Address.code op) cost s t ∧
      Ready L origin center bits next t := by
  cases op <;>
    simp only [BitRAM.next, hcode, Option.some.injEq, PricedStep.mk.injEq] at hnext
  all_goals try contradiction
  all_goals rcases hnext with ⟨rfl, rfl⟩
  all_goals simp only [Fits, registerCap, tapeCap, Nat.max_le] at hfit
  case literal r b =>
    obtain ⟨t, he, ht⟩ := literal_instruction input tape s h r b (by omega)
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case bitXor dst left right =>
    obtain ⟨cost, t, hc, he, ht⟩ := xor_instruction input tape s h dst left right
      (by omega) (by omega) (by omega)
    exact ⟨cost, t, by simp [instructionConstant]; omega, he, ht⟩
  case bitAnd dst left right =>
    obtain ⟨t, he, ht⟩ := and_instruction input tape s h dst left right
      (by omega) (by omega) (by omega)
    exact ⟨5, t, by simp [instructionConstant], he, ht⟩
  case bitNot dst src =>
    obtain ⟨t, he, ht⟩ := not_instruction input tape s h dst src (by omega) (by omega)
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case readSequential r =>
    obtain ⟨cost, t, hc, he, ht⟩ := readSequential_instruction input tape s h r (by omega)
      (by omega)
    exact ⟨cost, t, by simp [instructionConstant]; omega, he, ht⟩
  case inputLeft =>
    obtain ⟨t, he, ht⟩ := inputLeft_instruction input tape s h hinput
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case inputRight =>
    obtain ⟨t, he, ht⟩ := inputRight_instruction input tape s h (by omega)
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case addressPeek r =>
    obtain ⟨cost, t, hc, he, ht⟩ := addressPeek_instruction input tape s h r (by omega)
    exact ⟨cost, t, by simp [instructionConstant]; omega, he, ht⟩
  case addressIsEmpty r =>
    obtain ⟨t, he, ht⟩ := addressIsEmpty_instruction input tape s h r (by omega)
    exact ⟨5, t, by simp [instructionConstant], he, ht⟩
  case readTape t dst present =>
    have ht : t < L.tapeCount := by omega
    obtain ⟨u, he, hu⟩ := readTape_instruction input tape s h t dst present ht
      (by omega) (by omega) (le_of_lt (htapes t ht))
    exact ⟨_, u, by simp [instructionConstant]; omega, he, hu⟩
  case writeTape t src =>
    have ht : t < L.tapeCount := by omega
    obtain ⟨u, he, hu⟩ := writeTape_instruction input tape s h t src ht
      (by omega) (le_of_lt (htapes t ht))
    exact ⟨_, u, by simp [instructionConstant], he, hu⟩
  case eraseTape t =>
    have ht : t < L.tapeCount := by omega
    obtain ⟨u, he, hu⟩ := eraseTape_instruction input tape s h t ht (le_of_lt (htapes t ht))
    exact ⟨_, u, by simp [instructionConstant], he, hu⟩
  case tapeLeft t =>
    have ht : t < L.tapeCount := by omega
    obtain ⟨u, he, hu⟩ := tapeLeft_instruction input tape s h t ht (htapes t ht)
    exact ⟨4, u, by simp [instructionConstant], he, hu⟩
  case tapeRight t =>
    have ht : t < L.tapeCount := by omega
    obtain ⟨u, he, hu⟩ := tapeRight_instruction input tape s h t ht (le_of_lt (htapes t ht))
    exact ⟨4, u, by simp [instructionConstant], he, hu⟩
  case addressPush r =>
    obtain ⟨t, he, ht⟩ := addressPush_instruction input tape s h r (by omega)
    exact ⟨_, t, by simp [instructionConstant], he, ht⟩
  case addressPop =>
    obtain ⟨t, he, ht⟩ := addressPop_instruction input tape s h
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case addressClear =>
    obtain ⟨t, he, ht⟩ := addressClear_instruction input tape s h
    exact ⟨4, t, by simp [instructionConstant], he, ht⟩
  case readInput r =>
    obtain ⟨cost, t, hc, he, ht⟩ := readInput_instruction input tape s h r (by omega)
    refine ⟨cost, t, ?_, he, ht⟩
    unfold instructionConstant
    nlinarith
  case readMemory r =>
    obtain ⟨t, he, ht⟩ := readMemory_instruction input tape s h r (by omega)
    refine ⟨_, t, ?_, he, ht⟩
    unfold instructionConstant
    nlinarith
  case writeMemory r =>
    obtain ⟨t, he, ht⟩ := writeMemory_instruction input tape s h r (by omega)
    refine ⟨_, t, ?_, he, ht⟩
    unfold instructionConstant
    nlinarith
  case branch r yes no =>
    obtain ⟨t, he, ht⟩ := branch_instruction input tape s h r yes no (by omega)
    exact ⟨3, t, by simp [instructionConstant], he, ht⟩
  case jump pc =>
    obtain ⟨t, he, ht⟩ := jump_instruction input tape s h pc
    exact ⟨2, t, by simp [instructionConstant], he, ht⟩
  case randomBit r =>
    obtain ⟨t, he, ht⟩ := randomBit_instruction input tape s h r (by omega)
    exact ⟨8, t, by simp [instructionConstant], he, ht⟩
  case output r =>
    obtain ⟨t, he, ht⟩ := output_instruction input tape s h r (by omega)
    exact ⟨_, t, by simp [instructionConstant], he, ht⟩

end Maxwell.Cost.RealSimulation
