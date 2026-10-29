import Maxwell.Cost.TapeOps

/-! Clear a completed zero-origin word backwards, retaining its origin
until the blank sentinel is reached. The next parser receives a blank
tape at head zero without any uncharged pointer reset. -/

namespace Maxwell.Cost.TapeReset

def program (workTape : ℕ) : BitRAM := ⟨[
  .tapeLeft workTape, .readTape workTape 26 27,
  .branch 27 3 5, .eraseTape workTape, .jump 0,
  .tapeRight workTape, .halt]⟩

def retreat (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes workTape
      ⟨(s.tapes workTape).head - 1,
        Function.update (s.tapes workTape).cells ((s.tapes workTape).head - 1) none⟩
    registers := Function.update (Function.update s.registers 26 b) 27 true}

def finish (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    tapes := Function.update s.tapes workTape BitTape.blank
    registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem retreat_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b) :
    PricedSteps ((program workTape).next input randomTape) 6 s (retreat workTape s b) := by
  apply executeInstructions_sound (instructions := 5)
  simp [executeInstructions, BitRAM.next, program, hpc, hread,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, BitTape.write, retreat]

theorem finish_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hword : s.tapes workTape = BitTape.blank) :
    PricedSteps ((program workTape).next input randomTape) 5 s (finish workTape s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc, hword, BitTape.blank,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, finish]

theorem retreat_tape (workTape : ℕ) (s : BitRAMState) (bits : List Bool) (b : Bool)
    (htape : s.tapes workTape = BitTape.atEnd (bits ++ [b])) :
    (retreat workTape s b).tapes workTape = BitTape.atEnd bits := by
  apply BitTape.ext
  · simp [retreat, htape, BitTape.atEnd]
  · have heq := congrArg BitTape.cells (BitTape.erase_last bits b)
    simpa [retreat, htape, BitTape.beforeEnd, BitTape.atEnd,
      BitTape.ofList, BitTape.write] using heq

theorem finish_retreat (workTape : ℕ) (s : BitRAMState) (b : Bool) :
    finish workTape (retreat workTape s b) = finish workTape s := by
  simp [finish, retreat]
  funext i
  by_cases hi : i = 26 <;> by_cases hj : i = 27 <;>
    simp [hi, hj]

theorem steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.atEnd bits) :
    PricedSteps ((program workTape).next input randomTape)
      (6 * bits.length + 5) s (finish workTape s) := by
  induction bits using List.reverseRecOn generalizing s with
  | nil => exact finish_block workTape input randomTape s hpc (by simpa [BitTape.atEnd_nil] using hword)
  | append_singleton bits b ih =>
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b := by
      rw [hword]
      simpa [BitTape.beforeEnd, BitTape.atEnd, BitTape.read] using BitTape.beforeEnd_read bits b
    have hs := retreat_block workTape input randomTape s b hpc hread
    have hr := ih (retreat workTape s b) rfl (retreat_tape workTape s bits b hword)
    rw [finish_retreat] at hr
    convert hs.trans hr using 1
    simp
    omega

theorem finish_frame (workTape : ℕ) (s : BitRAMState) :
    TapeOps.Frame workTape workTape s (finish workTape s) := by
  simp [TapeOps.Frame, finish, Function.update_apply]
  constructor
  · intro i hi hi'; exact (hi hi').elim
  · intro i hi hj; simp [hi, hj]

theorem finish_tape (workTape : ℕ) (s : BitRAMState) :
    (finish workTape s).tapes workTape = BitTape.blank := by simp [finish]

theorem run (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.atEnd bits) :
    (runPriced ((program workTape).next input randomTape) (6 * bits.length + 6) s).finished =
        some (finish workTape s) ∧
      (runPriced ((program workTape).next input randomTape) (6 * bits.length + 6) s).instructions =
        6 * bits.length + 5 := by
  exact (steps workTape input randomTape bits s hpc hword).runPriced
    (by simp [BitRAM.next, program, finish])

end Maxwell.Cost.TapeReset
