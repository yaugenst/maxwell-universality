import Maxwell.Cost.Address
import Maxwell.Cost.Blocks

namespace Maxwell.Cost.MemoryBit

/-- Load the explicit binary address, then execute one charged memory
operation. Both construction and the full address traversal are counted. -/
def program (addressTape : ℕ) (operation : BitRAMInstruction) : BitRAM :=
  ⟨(Address.load addressTape).code.map (BitRAMInstruction.relocate 0 7) ++
    [operation, .halt]⟩

theorem contains_load (addressTape : ℕ) (operation : BitRAMInstruction) :
    (program addressTape operation).Contains (Address.load addressTape) 0 7 := by
  intro i
  fin_cases i <;> rfl

def ReadFrame (addressTape : ℕ) (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ addressTape → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → t.registers i = s.registers i)

/-- An indexed bit read uses a fixed program and exactly 7L+7 bit
operations, including the L-bit memory-address charge. -/
theorem read_steps (addressTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes addressTape = BitTape.shiftedEnd bits origin) :
    ∃ t, PricedSteps ((program addressTape (.readMemory 28)).next input randomTape)
        (7 * bits.length + 7) s t ∧
      t.pc = 8 ∧ t.address = bits ∧ t.registers 28 = s.memory (addressValue bits) ∧
      t.tapes addressTape = {BitTape.shifted bits origin with head := origin - 1} ∧
      ReadFrame addressTape s t := by
  obtain ⟨loaded, hs, hp, ha, hw, hf⟩ :=
    Address.load_steps addressTape input randomTape bits origin s hpc hword
  have hs' := (contains_load addressTape (.readMemory 28)).call input randomTape hs
    (by simp [Address.load, hp])
  simp only [BitRAMState.relocate, zero_add] at hs'
  let final := ({loaded with pc := 7} : BitRAMState).setRegister 28
    (loaded.memory (addressValue bits))
  have hread : PricedSteps ((program addressTape (.readMemory 28)).next input randomTape)
      (bits.length + 1) {loaded with pc := 7} final := by
    apply PricedSteps.step (extra := bits.length) (rest := PricedSteps.refl final)
    simp [program, Address.load, BitRAMInstruction.relocate, BitRAM.next, ha, final]
  refine ⟨final, ?_, rfl, ha, ?_, hw, ?_⟩
  · convert hs'.trans hread using 1
    omega
  · simp [final, hf.2.1]
  · rcases hf with ⟨hi, hm, hr, ho, ht, hg⟩
    refine ⟨hi, hm, hr, ho, ht, ?_⟩
    intro i h26 h27 h28
    simpa [final, h28] using hg i h26 h27

/-- A write preserves every other memory bit. Its address construction and
memory traversal cost exactly the same 7L+7 operations as a read. -/
theorem write_steps (addressTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes addressTape = BitTape.shiftedEnd bits origin) :
    ∃ t, PricedSteps ((program addressTape (.writeMemory 28)).next input randomTape)
        (7 * bits.length + 7) s t ∧
      t.pc = 8 ∧ t.address = bits ∧
      t.memory = Function.update s.memory (addressValue bits) (s.registers 28) ∧
      t.tapes addressTape = {BitTape.shifted bits origin with head := origin - 1} ∧
      t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
      (∀ i, i ≠ addressTape → t.tapes i = s.tapes i) ∧
      (∀ i, i ≠ 26 → i ≠ 27 → t.registers i = s.registers i) := by
  obtain ⟨loaded, hs, hp, ha, hw, hf⟩ :=
    Address.load_steps addressTape input randomTape bits origin s hpc hword
  have hs' := (contains_load addressTape (.writeMemory 28)).call input randomTape hs
    (by simp [Address.load, hp])
  simp only [BitRAMState.relocate, zero_add] at hs'
  let final := {loaded with
    pc := 8
    memory := Function.update loaded.memory (addressValue bits) (loaded.registers 28)}
  have hwrite : PricedSteps ((program addressTape (.writeMemory 28)).next input randomTape)
      (bits.length + 1) {loaded with pc := 7} final := by
    apply PricedSteps.step (extra := bits.length) (rest := PricedSteps.refl final)
    simp [program, Address.load, BitRAMInstruction.relocate, BitRAM.next, ha, final]
  rcases hf with ⟨hi, hm, hr, ho, ht, hg⟩
  refine ⟨final, ?_, rfl, ha, ?_, hw, hi, hr, ho, ht, hg⟩
  · convert hs'.trans hwrite using 1
    omega
  · simp [final, hm, hg 28 (by omega) (by omega)]

end Maxwell.Cost.MemoryBit
