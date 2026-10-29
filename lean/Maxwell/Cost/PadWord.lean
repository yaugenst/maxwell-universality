import Maxwell.Cost.WordTransfer

namespace Maxwell.Cost.PadWord

def bits : List Bool → List Bool
  | [] => [false]
  | b :: bs => b :: bs

@[simp] theorem value (xs : List Bool) : addressValue (bits xs) = addressValue xs := by
  cases xs <;> simp [bits, addressValue]

theorem nonempty (xs : List Bool) : 0 < (bits xs).length := by
  cases xs <;> simp [bits]

theorem length_le (xs : List Bool) : (bits xs).length ≤ xs.length + 1 := by
  cases xs <;> simp [bits]

def program (workTape : ℕ) : BitRAM := ⟨[
  .readTape workTape 26 27, .branch 27 4 2, .literal 26 false,
  .writeTape workTape 26, .halt]⟩

def finish (workTape : ℕ) (s : BitRAMState) (xs : List Bool) : BitRAMState :=
  {s with
    pc := 4
    registers := Function.update (Function.update s.registers 26 (xs.head?.getD false))
      27 xs.head?.isSome
    tapes := if xs.isEmpty then Function.update s.tapes workTape ((s.tapes workTape).write (some false))
      else s.tapes}

theorem simulation (workTape : ℕ) (origin : ℤ) (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hw : s.tapes workTape = BitTape.shifted xs origin) :
    ∃ cost, cost ≤ 5 ∧
      PricedSteps ((program workTape).next input tape) cost s (finish workTape s xs) ∧
      (finish workTape s xs).tapes workTape = BitTape.shifted (bits xs) origin ∧
      TapeOps.Frame workTape workTape s (finish workTape s xs) := by
  cases xs with
  | nil =>
    refine ⟨5, by omega, ?_, ?_, ?_⟩
    · apply executeInstructions_sound (instructions := 4)
      simp [executeInstructions, BitRAM.next, program, hpc, hw, BitTape.read, BitTape.shifted,
        finish, BitRAMState.setRegister, BitRAMState.setTape]
    · simp only [finish, List.isEmpty_nil, ↓reduceIte, Function.update_self, bits, hw]
      apply BitTape.ext
      · rfl
      · funext k
        by_cases hk : k = origin
        · subst k
          simp [BitTape.write, BitTape.shifted]
        · by_cases hle : origin ≤ k
          · have hgt : origin < k := by omega
            simp [BitTape.write, BitTape.shifted, hk, hle, hgt]
          · simp [BitTape.write, BitTape.shifted, hk, hle]
    · simp [TapeOps.Frame, finish]
      constructor <;> intros <;> simp_all
  | cons b bs =>
    refine ⟨3, by omega, ?_, ?_, ?_⟩
    · apply executeInstructions_sound (instructions := 2)
      simp [executeInstructions, BitRAM.next, program, hpc, hw, BitTape.read, BitTape.shifted,
        finish, BitRAMState.setRegister]
    · simpa [finish, bits] using hw
    · simp [TapeOps.Frame, finish]
      intros
      simp_all

end Maxwell.Cost.PadWord
