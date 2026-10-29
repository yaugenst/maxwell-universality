import Maxwell.Cost.Multiplication.Loop

namespace Maxwell.Cost.Address

open HornerMultiply (PrefixTape)

/-- Construct a random-access address by charged single-bit pushes. The
source is a little-endian word scanned from its most significant end. -/
def load (workTape : ℕ) : BitRAM := ⟨[
  .addressClear, .tapeLeft workTape, .readTape workTape 26 27,
  .branch 27 4 6, .addressPush 26, .jump 1, .halt]⟩

def advance (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 1
    address := b :: s.address
    registers := Function.update (Function.update s.registers 26 b) 27 true
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head - 1}}

def stop (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    registers := Function.update (Function.update s.registers 26 false) 27 false
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head - 1}}

def Frame (workTape : ℕ) (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ workTape → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.refl (workTape : ℕ) (s : BitRAMState) : Frame workTape s s := by simp [Frame]

theorem Frame.trans {workTape : ℕ} {s t u : BitRAMState}
    (h : Frame workTape s t) (k : Frame workTape t u) : Frame workTape s u := by
  rcases h with ⟨hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ki, km, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hn => (kt i hn).trans (ht i hn),
    fun i h26 h27 => (kg i h26 h27).trans (hg i h26 h27)⟩

theorem advance_frame (workTape : ℕ) (s : BitRAMState) (b : Bool) :
    Frame workTape s (advance workTape s b) := by
  simp [Frame, advance]
  constructor <;> intros <;> simp_all

theorem stop_frame (workTape : ℕ) (s : BitRAMState) : Frame workTape s (stop workTape s) := by
  simp [Frame, stop]
  constructor <;> intros <;> simp_all

theorem advance_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 1)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b) :
    PricedSteps ((load workTape).next input randomTape) 6 s (advance workTape s b) := by
  apply executeInstructions_sound (instructions := 5)
  simp [executeInstructions, load, BitRAM.next, hpc, hread, BitTape.read,
    advance, BitRAMState.setTape, BitRAMState.setRegister]

theorem stop_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = none) :
    PricedSteps ((load workTape).next input randomTape) 4 s (stop workTape s) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, load, BitRAM.next, hpc, hread, BitTape.read,
    stop, BitRAMState.setTape, BitRAMState.setRegister]

theorem advance_prefix (workTape : ℕ) (s : BitRAMState) (bits : List Bool)
    (origin : ℤ) (b : Bool) (h : PrefixTape (s.tapes workTape) (bits ++ [b]) origin) :
    PrefixTape ((advance workTape s b).tapes workTape) bits origin := by
  constructor
  · simp [advance, h.head]
    omega
  · simpa [advance] using h.left
  · intro k hk
    have hh := h.cells k (by simp; omega)
    simpa [advance, List.getElem_append_left hk] using hh

/-- The loop extends an existing address by exactly the represented prefix;
no uncharged address conversion is part of the machine execution. -/
theorem loop_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc = 1)
    (hword : PrefixTape (s.tapes workTape) bits origin) :
    ∃ t, PricedSteps ((load workTape).next input randomTape) (6 * bits.length + 4) s t ∧
      t.pc = 6 ∧ t.address = bits ++ s.address ∧
      t.tapes workTape = {s.tapes workTape with head := origin - 1} ∧ Frame workTape s t := by
  induction bits using List.reverseRecOn generalizing s with
  | nil =>
    refine ⟨stop workTape s, ?_, rfl, rfl, ?_, stop_frame workTape s⟩
    · simpa using stop_steps workTape input randomTape s hpc hword.nil_read
    · simp [stop, hword.head]
  | append_singleton bits b ih =>
    have hs := advance_steps workTape input randomTape s b hpc hword.last_read
    obtain ⟨t, ht, hp, ha, hw, hf⟩ := ih (advance workTape s b) rfl
      (advance_prefix workTape s bits origin b hword)
    refine ⟨t, ?_, hp, ?_, ?_, (advance_frame workTape s b).trans hf⟩
    · convert hs.trans ht using 1
      simp
      omega
    · simpa [advance, List.append_assoc] using ha
    · simpa [advance] using hw

/-- A fixed seven-instruction program loads every binary word in 6L+5
charged bit operations, preserving its cells and all external channels. -/
theorem load_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shiftedEnd bits origin) :
    ∃ t, PricedSteps ((load workTape).next input randomTape) (6 * bits.length + 5) s t ∧
      t.pc = 6 ∧ t.address = bits ∧
      t.tapes workTape = {BitTape.shifted bits origin with head := origin - 1} ∧
      Frame workTape s t := by
  let start := {s with pc := 1, address := []}
  have hs : PricedSteps ((load workTape).next input randomTape) 1 s start := by
    apply PricedSteps.step (rest := PricedSteps.refl start)
    simp [BitRAM.next, load, hpc, start]
  obtain ⟨t, ht, hp, ha, hw, hf⟩ := loop_steps workTape input randomTape bits origin start rfl
    (by simpa [start, hword] using PrefixTape.shiftedEnd bits origin)
  refine ⟨t, ?_, hp, ?_, ?_, ?_⟩
  · convert hs.trans ht using 1
    omega
  · simpa [start] using ha
  · simpa [start, hword, BitTape.shiftedEnd] using hw
  · exact (show Frame workTape s start by simp [Frame, start]).trans hf

end Maxwell.Cost.Address
