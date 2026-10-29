import Maxwell.Cost.PowerOfTwo

namespace Maxwell.Cost.NormalizeCoefficient.PadReverse

def padded (width : ℕ) (bits : List Bool) : List Bool :=
  bits ++ List.replicate (width - bits.length) false

theorem prepend_word (bits : List Bool) (origin : ℤ) (b : Bool) :
    ({BitTape.shifted bits origin with head := origin - 1}).write (some b) =
      BitTape.shifted (b :: bits) (origin - 1) := by
  apply BitTape.ext <;> try rfl
  funext p
  simp only [BitTape.write, BitTape.shifted]
  by_cases he : p = origin - 1
  · subst p; simp
  · rw [Function.update_of_ne he]
    by_cases hp : origin ≤ p
    · have hp' : origin - 1 ≤ p := by omega
      have hn : (p - (origin - 1)).toNat = (p - origin).toNat + 1 := by omega
      simp [hp, hp', hn]
    · have hp' : ¬origin - 1 ≤ p := by omega
      simp [hp, hp']

theorem erase_move_nil (origin : ℤ) :
    {(BitTape.shifted [] origin).write none with head := origin + 1} =
      BitTape.shifted [] (origin + 1) := by
  apply BitTape.ext <;> try rfl
  funext p
  simp [BitTape.write, BitTape.shifted]

def program : BitRAM := ⟨[
  .readTape 82 28 29, .branch 28 9 2,
  .readTape 4 26 27, .tapeLeft 83, .writeTape 83 26,
  .eraseTape 4, .tapeRight 4, .tapeRight 82, .jump 0, .halt]⟩

def nextState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update
      (Function.update (Function.update s.registers 28 false) 29 true)
        26 ((s.tapes 4).read.getD false)) 27 (s.tapes 4).read.isSome
    tapes := Function.update (Function.update (Function.update s.tapes
      83 (({s.tapes 83 with head := (s.tapes 83).head - 1}).write
        (some ((s.tapes 4).read.getD false))))
      4 {(s.tapes 4).write none with head := (s.tapes 4).head + 1})
      82 {s.tapes 82 with head := (s.tapes 82).head + 1}}

def exitState (s : BitRAMState) : BitRAMState :=
  {s with pc := 9, registers := Function.update (Function.update s.registers 28 true) 29 true}

def LoopFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 4 → i ≠ 82 → i ≠ 83 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) :
    LoopFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi hj hk => (kt i hi hj hk).trans (ht i hi hj hk),
    fun i hi hj hk hl => (kg i hi hj hk hl).trans (hg i hi hj hk hl)⟩

theorem next_frame (s : BitRAMState) : LoopFrame s (nextState s) := by
  simp [LoopFrame, nextState]
  constructor <;> intros <;> simp_all

theorem exit_frame (s : BitRAMState) : LoopFrame s (exitState s) := by
  simp [LoopFrame, exitState]
  intros; simp_all

theorem cycle (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hpc : s.pc = 0) (hread : (s.tapes 82).read = some false) :
    PricedSteps (program.next input tape) 11 s (nextState s) := by
  apply executeInstructions_sound (instructions := 9)
  simp [executeInstructions, BitRAM.next, program, hpc, hread, nextState,
    BitRAMState.setRegister, BitRAMState.setTape, BitTape.write]

theorem finish (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hpc : s.pc = 0) (hread : (s.tapes 82).read = some true) :
    PricedSteps (program.next input tape) 3 s (exitState s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hread, exitState,
    BitRAMState.setRegister]

end Maxwell.Cost.NormalizeCoefficient.PadReverse
