import Maxwell.Cost.TapeOps
import Maxwell.Cost.Blocks

namespace Maxwell.Cost.Increment

/-- The Boolean carry recurrence implemented below, including padded inputs. -/
def carryBits (carry : Bool) : List Bool → List Bool
  | [] => if carry then [true] else []
  | b :: rest => xor b carry :: carryBits (b && carry) rest

def bits (word : List Bool) : List Bool := carryBits true word

theorem carryBits_value (carry : Bool) (word : List Bool) :
    addressValue (carryBits carry word) = addressValue word + carry.toNat := by
  induction word generalizing carry with
  | nil => cases carry <;> simp [carryBits, addressValue]
  | cons b word ih =>
    simp only [carryBits, addressValue, ih]
    cases carry <;> cases b <;> simp <;> omega

theorem bits_value (word : List Bool) : addressValue (bits word) = addressValue word + 1 := by
  simpa [bits] using carryBits_value true word

theorem carryBits_length_le (carry : Bool) (word : List Bool) :
    (carryBits carry word).length ≤ word.length + 1 := by
  induction word generalizing carry with
  | nil => cases carry <;> simp [carryBits]
  | cons b word ih => simpa [carryBits] using Nat.add_le_add_right (ih (b && carry)) 1

theorem carryBits_length_ge (carry : Bool) (word : List Bool) :
    word.length ≤ (carryBits carry word).length := by
  induction word generalizing carry with
  | nil => simp
  | cons b word ih => simpa [carryBits] using Nat.add_le_add_right (ih (b && carry)) 1

theorem bits_length_le (word : List Bool) : (bits word).length ≤ word.length + 1 :=
  carryBits_length_le true word

theorem bits_length_ge (word : List Bool) : word.length ≤ (bits word).length :=
  carryBits_length_ge true word

/-- A fixed in-place incrementer. Registers 26 through 29 are its only scratch. -/
def program (workTape : ℕ) : BitRAM := ⟨[
  .literal 26 true,
  .readTape workTape 27 28,
  .branch 28 3 8,
  .bitXor 29 27 26,
  .bitAnd 26 27 26,
  .writeTape workTape 29,
  .tapeRight workTape,
  .jump 1,
  .branch 26 9 11,
  .writeTape workTape 26,
  .tapeRight workTape,
  .halt]⟩

theorem program_length (workTape : ℕ) : (program workTape).code.length = 12 := rfl

/-- The current word with an already written preceding and an unread suffix. -/
def cursor (preceding rest : List Bool) (origin : ℤ) : BitTape :=
  {BitTape.shifted (preceding ++ rest) origin with head := origin + preceding.length}

theorem cursor_read (preceding rest : List Bool) (origin : ℤ) :
    (cursor preceding rest origin).read = rest.head? := by
  simp [cursor, BitTape.read, BitTape.shifted, List.getElem?_append,
    List.head?_eq_getElem?]

private theorem shifted_write_set (word : List Bool) (origin : ℤ) (n : ℕ) (b : Bool)
    (hn : n < word.length) :
    ({BitTape.shifted word origin with head := origin + n}).write (some b) =
      {BitTape.shifted (word.set n b) origin with head := origin + n} := by
  apply BitTape.ext
  · rfl
  · funext p
    simp only [BitTape.write, BitTape.shifted]
    by_cases heq : p = origin + (n : ℤ)
    · subst p; simp [hn]
    · rw [Function.update_of_ne heq]
      by_cases hp : origin ≤ p
      · have hi : n ≠ (p - origin).toNat := by omega
        simp [hp, List.getElem?_set_ne hi]
      · simp [hp]

theorem cursor_write_move (preceding rest : List Bool) (origin : ℤ) (a b : Bool) :
    {(cursor preceding (a :: rest) origin).write (some b) with
      head := (cursor preceding (a :: rest) origin).head + 1} =
      cursor (preceding ++ [b]) rest origin := by
  have hw := shifted_write_set (preceding ++ a :: rest) origin preceding.length b (by simp)
  change {({BitTape.shifted (preceding ++ a :: rest) origin with
    head := origin + preceding.length}).write (some b) with
    head := origin + preceding.length + 1} = _
  rw [hw]
  simp [cursor, List.set_append_right, List.append_assoc, BitTape.shifted, add_assoc]

/-- Complete preservation contract, including the sign and ambient channels. -/
def Frame (workTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ workTape → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem Frame.refl (workTape : ℕ) (s : BitRAMState) : Frame workTape s s := by simp [Frame]

theorem Frame.trans {workTape : ℕ} {s t u : BitRAMState}
    (h : Frame workTape s t) (k : Frame workTape t u) : Frame workTape s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hw => (kt i hw).trans (ht i hw),
    fun i h26 h27 h28 h29 => (kg i h26 h27 h28 h29).trans (hg i h26 h27 h28 h29)⟩

theorem next_frame (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : (program workTape).next input randomTape s = some step) :
    Frame workTape s step.state := by
  have hlt := (program workTape).next_code_present input randomTape s step h
  rw [program_length] at hlt
  interval_cases hp : s.pc <;> simp [BitRAM.next, program, hp] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape, Function.update_apply]
  all_goals intros; simp_all

theorem execution_frame (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState}
    (h : PricedSteps ((program workTape).next input randomTape) cost s t) : Frame workTape s t := by
  induction h with
  | refl s => exact Frame.refl workTape s
  | step h rest ih => exact (next_frame workTape input randomTape h).trans ih

def round (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 1
    registers := Function.update (Function.update
      (Function.update (Function.update s.registers 27 b) 28 true)
        29 (xor b (s.registers 26))) 26 (b && s.registers 26)
    tapes := Function.update s.tapes workTape
      {(s.tapes workTape).write (some (xor b (s.registers 26))) with
        head := (s.tapes workTape).head + 1}}

def stopped (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 11
    registers := Function.update (Function.update s.registers 27 false) 28 false
    tapes := if s.registers 26 then Function.update s.tapes workTape
      {(s.tapes workTape).write (some true) with head := (s.tapes workTape).head + 1}
      else s.tapes}

theorem round_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 1)
    (hread : (s.tapes workTape).read = some b) :
    PricedSteps ((program workTape).next input randomTape) 8 s (round workTape s b) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions, BitRAM.next, program, hpc, hread, round,
    BitRAMState.setRegister, BitRAMState.setTape, BitTape.write]

theorem stop_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (hread : (s.tapes workTape).read = none) :
    PricedSteps ((program workTape).next input randomTape)
      (if s.registers 26 then 6 else 4) s (stopped workTape s) := by
  cases hc : s.registers 26
  · apply executeInstructions_sound (instructions := 3)
    simp [executeInstructions, BitRAM.next, program, hpc, hread, stopped, hc,
      BitRAMState.setRegister]
  · apply executeInstructions_sound (instructions := 5)
    simp [executeInstructions, BitRAM.next, program, hpc, hread, stopped, hc,
      BitRAMState.setRegister, BitRAMState.setTape, BitTape.write]

/-- All unread bits are visited, even after the carry clears, so the final
head is at the exact end and padded input widths are preserved. -/
theorem loop (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (remaining preceding : List Bool) (origin : ℤ) (s : BitRAMState)
    (hpc : s.pc = 1) (hword : s.tapes workTape = cursor preceding remaining origin) :
    ∃ cost t, cost ≤ 8 * remaining.length + 6 ∧
      PricedSteps ((program workTape).next input randomTape) cost s t ∧ t.pc = 11 ∧
      t.tapes workTape = BitTape.shiftedEnd
        (preceding ++ carryBits (s.registers 26) remaining) origin := by
  induction remaining generalizing preceding s with
  | nil =>
    have hread : (s.tapes workTape).read = none := by rw [hword, cursor_read]; rfl
    refine ⟨_, stopped workTape s, ?_, stop_block workTape input randomTape s hpc hread, rfl, ?_⟩
    · cases s.registers 26 <;> simp
    · cases hc : s.registers 26
      · simpa [stopped, hc, carryBits, cursor, BitTape.shiftedEnd] using hword
      · have hw : s.tapes workTape = BitTape.shiftedEnd preceding origin := by
          simpa [cursor, BitTape.shiftedEnd] using hword
        simpa [stopped, hc, carryBits, hw] using
          BitTape.shiftedEnd_append_write preceding origin true
  | cons b remaining ih =>
    have hread : (s.tapes workTape).read = some b := by rw [hword, cursor_read]; rfl
    have hr := round_block workTape input randomTape s b hpc hread
    have hw : (round workTape s b).tapes workTape =
        cursor (preceding ++ [xor b (s.registers 26)]) remaining origin := by
      simp only [round, Function.update_self, hword]
      exact cursor_write_move preceding remaining origin b (xor b (s.registers 26))
    obtain ⟨cost, t, hc, ht, hp, hwout⟩ :=
      ih (preceding ++ [xor b (s.registers 26)]) (round workTape s b) rfl hw
    refine ⟨8 + cost, t, by simp only [List.length_cons]; omega, hr.trans ht, hp, ?_⟩
    simpa [carryBits, round, List.append_assoc] using hwout

/-- Exact in-place increment by twelve fixed Boolean instructions, with all
reads, carry gates, writes, head moves and jumps included in the cost. -/
theorem simulation (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : BitRAMState)
    (hpc : s.pc = 0) (hword : s.tapes workTape = BitTape.shifted word origin) :
    ∃ cost t, cost ≤ 8 * word.length + 7 ∧
      PricedSteps ((program workTape).next input randomTape) cost s t ∧
      t.pc = 11 ∧ t.tapes workTape = BitTape.shiftedEnd (bits word) origin ∧
      Frame workTape s t := by
  have hinit : PricedSteps ((program workTape).next input randomTape) 1 s
      (s.setRegister 26 true) := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, hpc]
  obtain ⟨cost, t, hc, ht, hp, hw⟩ := loop workTape input randomTape word [] origin
    (s.setRegister 26 true) (by simp [BitRAMState.setRegister, hpc])
    (by simpa [BitRAMState.setRegister, cursor, BitTape.shifted] using hword)
  have hs := hinit.trans ht
  exact ⟨1 + cost, t, by omega, hs, hp,
    by simpa [bits, BitRAMState.setRegister] using hw,
    execution_frame workTape input randomTape hs⟩

theorem run (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : BitRAMState)
    (hpc : s.pc = 0) (hword : s.tapes workTape = BitTape.shifted word origin) :
    ∃ t, (runPriced ((program workTape).next input randomTape) (8 * word.length + 8) s).finished = some t ∧
      (runPriced ((program workTape).next input randomTape) (8 * word.length + 8) s).instructions ≤
        8 * word.length + 7 ∧
      t.tapes workTape = BitTape.shiftedEnd (bits word) origin ∧ Frame workTape s t := by
  obtain ⟨cost, t, hc, hs, hp, hw, hf⟩ := simulation workTape input randomTape word origin s hpc hword
  have hh : (program workTape).next input randomTape t = none := by simp [BitRAM.next, program, hp]
  have hrun := hs.runPriced_ge hh (8 * word.length + 8) (by omega)
  exact ⟨t, hrun.1, by simpa [hrun.2] using hc, hw, hf⟩

end Maxwell.Cost.Increment
