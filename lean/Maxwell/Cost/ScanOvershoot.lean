import Maxwell.Cost.Scan
import Maxwell.Cost.Link

/-! A two-phase rewind from blank overshoot after a nonempty word. The
routine first finds the word, then rewinds to its first cell. Empty words
are excluded because an entirely blank tape has no discoverable origin. -/

namespace Maxwell.Cost.RewindOvershoot

def preamble (workTape : ℕ) : List BitRAMInstruction :=
  [.tapeLeft workTape, .readTape workTape 24 25, .branch 25 3 0]

def program (workTape : ℕ) : BitRAM :=
  BitRAM.link (preamble workTape) (Rewind.program workTape) 8 [.halt]

def seekState (workTape : ℕ) (s : BitRAMState) (symbol : Option Bool) : BitRAMState :=
  {s with
    pc := if symbol.isSome then 3 else 0
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head - 1}
    registers := Function.update (Function.update s.registers 24 (symbol.getD false)) 25 symbol.isSome}

def finish (workTape : ℕ) (origin : ℤ) (s : BitRAMState) : BitRAMState :=
  {Rewind.finishAt workTape origin s with pc := 8}

theorem seek_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (symbol : Option Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = symbol) :
    PricedSteps ((program workTape).next input randomTape) 4 s (seekState workTape s symbol) := by
  apply executeInstructions_sound (instructions := 3)
  cases symbol <;>
    simp [executeInstructions, BitRAM.next, program, BitRAM.link, preamble, Rewind.program,
      BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, hpc, seekState]

theorem finish_seek (workTape : ℕ) (origin : ℤ) (s : BitRAMState)
    (symbol : Option Bool) :
    finish workTape origin (seekState workTape s symbol) = finish workTape origin s := by
  simp [finish, Rewind.finishAt, seekState]
  funext i
  by_cases hi : i = 24 <;> by_cases hj : i = 25 <;> simp [hi, hj]

/-- The exact cost depends on traversed cells; the machine receives no
unbounded integer origin, length, or overshoot as an instruction argument. -/
theorem steps (workTape : ℕ) (origin : ℤ) (input : List Bool) (randomTape : ℕ → Bool)
    (length overshoot : ℕ) (hlength : 0 < length) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes workTape).head = origin + length + overshoot)
    (hblank : (s.tapes workTape).cells (origin - 1) = none)
    (hpresent : ∀ k < length, ∃ b, (s.tapes workTape).cells (origin + k) = some b)
    (hgap : ∀ k < overshoot, (s.tapes workTape).cells (origin + length + k) = none) :
    PricedSteps ((program workTape).next input randomTape)
      (4 * (length + overshoot) + 6) s (finish workTape origin s) := by
  induction overshoot generalizing s with
  | zero =>
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hlength.ne'
    obtain ⟨b, hb⟩ := hpresent l (by omega)
    have hposition : (s.tapes workTape).head - 1 = origin + l := by
      rw [hhead]
      push_cast
      omega
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b := by
      simpa only [hposition] using hb
    have hs := seek_block workTape input randomTape s (some b) hpc hread
    let localStart := {seekState workTape s (some b) with pc := 0}
    have hw := Rewind.stepsAt workTape origin input randomTape l localStart rfl
      (by simpa only [localStart, seekState, Function.update_self] using hposition)
      (by simpa [localStart, seekState] using hblank)
      (by intro k hk; simpa [localStart, seekState] using hpresent k (by omega))
    have hlinked := hw.link (preamble workTape) 8 [.halt]
    have hstart : localStart.relocate (preamble workTape).length = seekState workTape s (some b) := by
      simp [localStart, BitRAMState.relocate, preamble, seekState]
    rw [hstart] at hlinked
    have hreturn : PricedSteps ((program workTape).next input randomTape) 1
        ((Rewind.finishAt workTape origin localStart).relocate (preamble workTape).length)
        (finish workTape origin localStart) := by
      exact PricedSteps.step
        (BitRAM.link_return (preamble workTape) (Rewind.program workTape) 8 [.halt]
          input randomTape (Rewind.finishAt workTape origin localStart)
          (by simp [Rewind.finishAt, Rewind.program])) (PricedSteps.refl _)
    have hf : finish workTape origin localStart = finish workTape origin s := by
      change finish workTape origin (seekState workTape s (some b)) = _
      exact finish_seek workTape origin s (some b)
    rw [hf] at hreturn
    convert (hs.trans hlinked).trans hreturn using 1
    omega
  | succ overshoot ih =>
    have hposition : (s.tapes workTape).head - 1 = origin + length + overshoot := by
      rw [hhead]
      push_cast
      omega
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = none := by
      simpa only [hposition] using hgap overshoot (by omega)
    have hs := seek_block workTape input randomTape s none hpc hread
    have ht := ih (seekState workTape s none) rfl
      (by simpa only [seekState, Function.update_self] using hposition)
      (by simpa [seekState] using hblank)
      (by intro k hk; simpa [seekState] using hpresent k hk)
      (by intro k hk; simpa [seekState] using hgap k (by omega))
    rw [finish_seek] at ht
    convert hs.trans ht using 1
    omega

theorem run (workTape : ℕ) (origin : ℤ) (input : List Bool) (randomTape : ℕ → Bool)
    (length overshoot : ℕ) (hlength : 0 < length) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes workTape).head = origin + length + overshoot)
    (hblank : (s.tapes workTape).cells (origin - 1) = none)
    (hpresent : ∀ k < length, ∃ b, (s.tapes workTape).cells (origin + k) = some b)
    (hgap : ∀ k < overshoot, (s.tapes workTape).cells (origin + length + k) = none) :
    (runPriced ((program workTape).next input randomTape)
      (4 * (length + overshoot) + 7) s).finished = some (finish workTape origin s) ∧
    (runPriced ((program workTape).next input randomTape)
      (4 * (length + overshoot) + 7) s).instructions = 4 * (length + overshoot) + 6 := by
  exact (steps workTape origin input randomTape length overshoot hlength s hpc hhead
    hblank hpresent hgap).runPriced
      (by simp [BitRAM.next, program, BitRAM.link, preamble, Rewind.program, finish,
        Rewind.finishAt])

end Maxwell.Cost.RewindOvershoot
