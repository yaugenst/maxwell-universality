import Maxwell.Cost.TapeReset
import Maxwell.Cost.TrimShifted

namespace Maxwell.Cost.TapeReset

def finishAt (workTape : ℕ) (origin : ℤ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    tapes := Function.update s.tapes workTape {BitTape.blank with head := origin}
    registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem finishAt_block (workTape : ℕ) (origin : ℤ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = {BitTape.blank with head := origin}) :
    PricedSteps ((program workTape).next input randomTape) 5 s (finishAt workTape origin s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc, hword, BitTape.blank,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, finishAt]

theorem retreat_shifted (workTape : ℕ) (s : BitRAMState) (bits : List Bool) (b : Bool) (origin : ℤ)
    (htape : s.tapes workTape = BitTape.shiftedEnd (bits ++ [b]) origin) :
    (retreat workTape s b).tapes workTape = BitTape.shiftedEnd bits origin := by
  apply BitTape.ext
  · simp [retreat, htape, BitTape.shiftedEnd]
    omega
  · have heq := congrArg BitTape.cells (BitTape.shifted_erase_last bits b origin)
    simpa [retreat, htape, BitTape.shiftedBeforeEnd, BitTape.shiftedEnd,
      BitTape.shifted, BitTape.write] using heq

theorem finishAt_retreat (workTape : ℕ) (origin : ℤ) (s : BitRAMState) (b : Bool) :
    finishAt workTape origin (retreat workTape s b) = finishAt workTape origin s := by
  simp [finishAt, retreat]
  funext i
  by_cases hi : i = 26 <;> by_cases hj : i = 27 <;> simp [hi, hj]

theorem shifted_steps (workTape : ℕ) (origin : ℤ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shiftedEnd bits origin) :
    PricedSteps ((program workTape).next input randomTape)
      (6 * bits.length + 5) s (finishAt workTape origin s) := by
  induction bits using List.reverseRecOn generalizing s with
  | nil =>
    exact finishAt_block workTape origin input randomTape s hpc
      (by simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using hword)
  | append_singleton bits b ih =>
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b := by
      rw [hword]
      simpa [BitTape.shiftedBeforeEnd, BitTape.shiftedEnd, BitTape.read] using
        BitTape.shiftedBeforeEnd_read bits b origin
    have hs := retreat_block workTape input randomTape s b hpc hread
    have hr := ih (retreat workTape s b) rfl (retreat_shifted workTape s bits b origin hword)
    rw [finishAt_retreat] at hr
    convert hs.trans hr using 1
    simp
    omega

theorem finishAt_frame (workTape : ℕ) (origin : ℤ) (s : BitRAMState) :
    TapeOps.Frame workTape workTape s (finishAt workTape origin s) := by
  simp [TapeOps.Frame, finishAt, Function.update_apply]
  constructor
  · intro i hi hi'; exact (hi hi').elim
  · intro i hi hj; simp [hi, hj]

end Maxwell.Cost.TapeReset
