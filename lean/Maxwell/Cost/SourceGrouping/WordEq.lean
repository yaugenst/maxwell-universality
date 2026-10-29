import Maxwell.Cost.Copy

namespace Maxwell.Cost.SourceGrouping.WordEq

/-- Compare the two finite words without erasing either. End markers are
compared as well as Boolean values, so zero padding is not silently ignored. -/
def program : BitRAM := ⟨[
  .literal 31 true,
  .readTape 15 26 27, .readTape 22 28 29,
  .bitXor 30 27 29, .bitNot 30 30, .bitAnd 31 31 30,
  .bitXor 30 26 28, .bitNot 30 30, .bitAnd 31 31 30,
  .branch 27 10 11, .tapeRight 15,
  .branch 29 12 13, .tapeRight 22,
  .branch 27 1 14, .branch 29 1 15, .halt]⟩

def frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 15 → i ≠ 22 → t.tapes i = s.tapes i) ∧
  (∀ i, i < 26 ∨ 31 < i → t.registers i = s.registers i)

theorem frame_refl (s : BitRAMState) : frame s s := by simp [frame]
theorem frame_trans {s t u : BitRAMState} (h : frame s t) (k : frame t u) : frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h15 h22 => (kt i h15 h22).trans (ht i h15 h22),
    fun i hi => (kg i hi).trans (hg i hi)⟩

def advance (s : BitRAMState) (x y : Option Bool) : BitRAMState :=
  {s with
    pc := if x.isSome || y.isSome then 1 else 15
    registers := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update s.registers 26 (x.getD false)) 27 x.isSome)
        28 (y.getD false)) 29 y.isSome) 30 (!(xor (x.getD false) (y.getD false))))
          31 (s.registers 31 && (x == y))
    tapes := Function.update (Function.update s.tapes 15
      {s.tapes 15 with head := (s.tapes 15).head + (if x.isSome then 1 else 0)}) 22
      {s.tapes 22 with head := (s.tapes 22).head + (if y.isSome then 1 else 0)}}

def price (x y : Option Bool) : ℕ := if x.isSome then (if y.isSome then 15 else 14) else 15

set_option maxHeartbeats 4000000 in
theorem block (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState)
    (x y : Option Bool) (hpc : s.pc = 1)
    (hx : (s.tapes 15).read = x) (hy : (s.tapes 22).read = y)
    (hpresent : x.isSome || y.isSome = true) :
    PricedSteps (program.next input randomTape) (price x y) s (advance s x y) := by
  cases x with
  | none =>
    cases y with
    | none => simp at hpresent
    | some y =>
      apply executeInstructions_sound (instructions := 13)
      cases y <;> cases hs : s.registers 31 <;>
        simp [executeInstructions, BitRAM.next, program, hpc, hx, hy, advance, price,
          BitRAMState.setRegister, BitRAMState.setTape, hs] <;>
        funext i <;> by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;> simp [h30, h31]
  | some x =>
    cases y with
    | none =>
      apply executeInstructions_sound (instructions := 12)
      cases x <;> cases hs : s.registers 31 <;>
        simp [executeInstructions, BitRAM.next, program, hpc, hx, hy, advance, price,
          BitRAMState.setRegister, BitRAMState.setTape, hs] <;>
        funext i <;> by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;> simp [h30, h31]
    | some y =>
      apply executeInstructions_sound (instructions := 13)
      cases x <;> cases y <;> cases hs : s.registers 31 <;>
        simp [executeInstructions, BitRAM.next, program, hpc, hx, hy, advance, price,
          BitRAMState.setRegister, BitRAMState.setTape, hs] <;>
        funext i <;> by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;> simp [h30, h31]

theorem stop (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState)
    (hpc : s.pc = 1) (hx : (s.tapes 15).read = none) (hy : (s.tapes 22).read = none) :
    PricedSteps (program.next input randomTape) 14 s (advance s none none) := by
  apply executeInstructions_sound (instructions := 12)
  cases hs : s.registers 31 <;>
    simp [executeInstructions, BitRAM.next, program, hpc, hx, hy, advance,
      BitRAMState.setRegister, BitRAMState.setTape, hs] <;>
        funext i <;> by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;> simp [h30, h31]

theorem advance_frame (s : BitRAMState) (x y : Option Bool) : frame s (advance s x y) := by
  simp [frame, advance]
  constructor
  · intro i hi hj
    simp [hi, hj]
  · intro i hi
    have h26 : i ≠ 26 := by omega
    have h27 : i ≠ 27 := by omega
    have h28 : i ≠ 28 := by omega
    have h29 : i ≠ 29 := by omega
    have h30 : i ≠ 30 := by omega
    have h31 : i ≠ 31 := by omega
    simp [h26, h27, h28, h29, h30, h31]

/-- The loop consumes only represented cells and returns the exact list
comparison. Its linear bound includes both terminal blank reads. -/
theorem loop (input : List Bool) (randomTape : ℕ → Bool) (xs ys : List Bool)
    (s : BitRAMState) (hpc : s.pc = 1)
    (hx : TapeRepresents (s.tapes 15) xs) (hy : TapeRepresents (s.tapes 22) ys) :
    ∃ cost t, cost ≤ 15 * (xs.length + ys.length + 1) ∧
      PricedSteps (program.next input randomTape) cost s t ∧ t.pc = 15 ∧
      t.registers 31 = (s.registers 31 && (xs == ys)) ∧
      t.tapes 15 = {s.tapes 15 with head := (s.tapes 15).head + xs.length} ∧
      t.tapes 22 = {s.tapes 22 with head := (s.tapes 22).head + ys.length} ∧ frame s t := by
  induction xs generalizing ys s with
  | nil =>
    induction ys generalizing s with
    | nil =>
      refine ⟨14, advance s none none, by simp,
        stop input randomTape s hpc hx.read hy.read, rfl, ?_, ?_, ?_, advance_frame _ _ _⟩ <;>
        simp [advance]
    | cons y ys ih =>
      have hb := block input randomTape s none (some y) hpc hx.read hy.read (by simp)
      have hnx : TapeRepresents ((advance s none (some y)).tapes 15) [] := by
        simpa [advance] using hx
      have hny : TapeRepresents ((advance s none (some y)).tapes 22) ys := by
        simpa [advance] using hy.moveRight
      obtain ⟨c, t, hc, ht, hp, hg, h15, h22, hf⟩ := ih _ rfl hnx hny
      refine ⟨15 + c, t, by simp only [List.length_cons, List.length_nil] at *; omega,
        hb.trans ht, hp, ?_, ?_, ?_, frame_trans (advance_frame _ _ _) hf⟩
      · simpa [advance] using hg
      · simpa [advance] using h15
      · simpa [advance, Nat.cast_add, add_assoc, add_comm] using h22
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hb := block input randomTape s (some x) none hpc hx.read hy.read (by simp)
      have hnx : TapeRepresents ((advance s (some x) none).tapes 15) xs := by
        simpa [advance] using hx.moveRight
      have hny : TapeRepresents ((advance s (some x) none).tapes 22) [] := by
        simpa [advance] using hy
      obtain ⟨c, t, hc, ht, hp, hg, h15, h22, hf⟩ := ih [] _ rfl hnx hny
      refine ⟨14 + c, t, by simp only [List.length_cons, List.length_nil] at *; omega,
        hb.trans ht, hp, ?_, ?_, ?_, frame_trans (advance_frame _ _ _) hf⟩
      · simpa [advance] using hg
      · simpa [advance, Nat.cast_add, add_assoc, add_comm] using h15
      · simpa [advance] using h22
    | cons y ys =>
      have hb := block input randomTape s (some x) (some y) hpc hx.read hy.read (by simp)
      have hnx : TapeRepresents ((advance s (some x) (some y)).tapes 15) xs := by
        simpa [advance] using hx.moveRight
      have hny : TapeRepresents ((advance s (some x) (some y)).tapes 22) ys := by
        simpa [advance] using hy.moveRight
      obtain ⟨c, t, hc, ht, hp, hg, h15, h22, hf⟩ := ih ys _ rfl hnx hny
      refine ⟨15 + c, t, by simp only [List.length_cons] at *; omega,
        hb.trans ht, hp, ?_, ?_, ?_, frame_trans (advance_frame _ _ _) hf⟩
      · simpa [advance, Bool.and_assoc] using hg
      · simpa [advance, Nat.cast_add, add_assoc, add_comm] using h15
      · simpa [advance, Nat.cast_add, add_assoc, add_comm] using h22

theorem simulation (input : List Bool) (randomTape : ℕ → Bool) (xs ys : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hx : s.tapes 15 = BitTape.ofList xs) (hy : s.tapes 22 = BitTape.ofList ys) :
    ∃ cost t, cost ≤ 15 * (xs.length + ys.length + 1) + 1 ∧
      PricedSteps (program.next input randomTape) cost s t ∧ t.pc = 15 ∧
      t.registers 31 = (xs == ys) ∧
      t.tapes 15 = BitTape.atEnd xs ∧ t.tapes 22 = BitTape.atEnd ys ∧ frame s t := by
  have hi : PricedSteps (program.next input randomTape) 1 s (s.setRegister 31 true) := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, hpc]
  obtain ⟨c, t, hc, ht, hp, hg, h15, h22, hf⟩ := loop input randomTape xs ys
    (s.setRegister 31 true) (by simp [BitRAMState.setRegister, hpc])
    (by simpa [BitRAMState.setRegister, hx, BitTape.shifted, BitTape.ofList] using BitTape.shifted_represents xs 0)
    (by simpa [BitRAMState.setRegister, hy, BitTape.shifted, BitTape.ofList] using BitTape.shifted_represents ys 0)
  refine ⟨1 + c, t, by omega, hi.trans ht, hp, ?_, ?_, ?_, ?_⟩
  · simpa [BitRAMState.setRegister] using hg
  · simpa [BitRAMState.setRegister, hx, BitTape.atEnd, BitTape.ofList] using h15
  · simpa [BitRAMState.setRegister, hy, BitTape.atEnd, BitTape.ofList] using h22
  · apply frame_trans (t := s.setRegister 31 true) _ hf
    simp [frame, BitRAMState.setRegister]
    intro i hi
    have hn : i ≠ 31 := by omega
    simp [hn]

end Maxwell.Cost.SourceGrouping.WordEq
