import Maxwell.Cost.IndexedAddress
import Maxwell.Cost.Array

namespace Maxwell.Cost.ArrayAccess
open Structured

def readCode : Code := .seq IndexedAddress.code (.call MemoryWord.readProgram)
def writeCode : Code := .seq IndexedAddress.code (.call MemoryWord.writeProgram)
def readProgram : BitRAM := readCode.compile
def writeProgram : BitRAM := writeCode.compile

def costCap (width index base : List Bool) (wordWidth : ℕ) : ℕ :=
  1000 * (width.length + index.length + base.length + 5)^2 +
    wordWidth * (15 * (width.length + index.length + base.length + 1 + wordWidth) + 24) + 4

/-- Outside the explicit arithmetic, address and payload tapes, an indexed
access preserves all metadata, caller signs, and sequential channels. -/
def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ i = 8 ∨ 10 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi, hr, ho, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hh => (kt i hh).trans (ht i hh),
    fun i h15 h24 h25 h26 h27 h28 h29 =>
      (kg i h15 h24 h25 h26 h27 h28 h29).trans (hg i h15 h24 h25 h26 h27 h28 h29)⟩

theorem Frame.of_address {s t : BitRAMState} (h : IndexedAddress.Frame s t) : Frame s t := by
  rcases h with ⟨_, hi, _, hr, ho, ht, hg⟩
  exact ⟨hi, hr, ho, fun i hh => ht i (by omega) (by omega) (by omega),
    fun i h15 h24 h25 h26 h27 _ _ => hg i h15 h24 h25 h26 h27⟩

theorem Frame.of_read {s t : BitRAMState} (h : MemoryWord.Frame s t) : Frame s t := by
  rcases h with ⟨hi, _, hr, ho, _, ht, hg⟩
  exact ⟨hi, hr, ho, fun i hh => ht i (by omega) (by omega) (by omega),
    fun i _ _ _ h26 h27 h28 h29 => hg i h26 h27 h28 h29⟩

theorem Frame.of_write {s t : BitRAMState} (h : MemoryWord.WriteFrame s t) : Frame s t := by
  rcases h with ⟨hi, hr, ho, _, ht, hg⟩
  exact ⟨hi, hr, ho, fun i hh => ht i (by omega) (by omega),
    fun i _ _ _ h26 h27 h28 h29 => hg i h26 h27 h28 h29⟩

/-- The complete initial tape contract. Width/base words are reusable;
only the index word is consumed by address calculation. -/
structure Ready (s : BitRAMState) (width index base : List Bool)
    (ao wo zo yo io bo savedOrigin : ℤ) : Prop where
  zero : s.tapes 0 = {BitTape.blank with head := ao}
  width : s.tapes 1 = BitTape.shifted width wo
  scratch : s.tapes 2 = {BitTape.blank with head := zo}
  multiply : s.tapes 3 = {BitTape.blank with head := yo}
  index : s.tapes 5 = BitTape.shifted index io
  base : s.tapes 8 = BitTape.shifted base bo
  saved : s.tapes 9 = {BitTape.blank with head := savedOrigin}

/-- Scratch and reusable operands after either access. -/
structure Restored (s : BitRAMState) (width base : List Bool) (yo bo savedOrigin : ℤ) : Prop where
  zero : ∃ origin, s.tapes 0 = {BitTape.blank with head := origin}
  width : ∃ origin, s.tapes 1 = BitTape.shifted width origin
  scratch : ∃ origin, s.tapes 2 = {BitTape.blank with head := origin}
  multiply : s.tapes 3 = {BitTape.blank with head := yo}
  base : s.tapes 8 = BitTape.shifted base bo
  saved : s.tapes 9 = {BitTape.blank with head := savedOrigin}

theorem Restored.place {s : Store} {width base : List Bool} {yo bo savedOrigin : ℤ}
    (h : Restored s.val width base yo bo savedOrigin) (pc : ℕ) :
    Restored (s.place pc) width base yo bo savedOrigin :=
  ⟨h.zero, h.width, h.scratch, h.multiply, h.base, h.saved⟩

theorem address_length_le (width index base : List Bool) :
    (addressValue base + addressValue width * addressValue index).bits.length ≤
      width.length + index.length + base.length + 1 := by
  have hp := IndexedAddress.product_length_le width index
  have hs := IndexedAddress.sum_length_le base (addressValue width * addressValue index).bits
  rw [addressValue_bits] at hs
  omega

/-- Read an array entry after computing its address by the compiled binary
arithmetic, with one common charged execution for both stages. -/
theorem read_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index base clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (ao wo zo yo io bo savedOrigin clockOrigin outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store)
    (hready : Ready s.val width index base ao wo zo yo io bo savedOrigin)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words)
    (h6 : s.val.tapes 6 = BitTape.shifted clock clockOrigin)
    (h7 : s.val.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ cost t finalAddress addressOrigin,
      cost ≤ costCap width index base (addressValue width) ∧
      Executes input tape readCode cost s t ∧
      t.val.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue base + (i.val + 1) * addressValue width ∧
      finalAddress.length ≤ width.length + index.length + base.length + 1 + addressValue width ∧
      t.val.tapes 6 = BitTape.shiftedEnd clock clockOrigin ∧
      t.val.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      t.val.memory = s.val.memory ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) words ∧
      Restored t.val width base (yo + index.length) bo (savedOrigin + width.length) ∧ Frame s.val t.val := by
  obtain ⟨acost, a, ro, so, addressOrigin, widthOrigin, hacost, ha, ha0, ha1, ha2, ha3,
    ha5, ha8, ha9, haf⟩ :=
    IndexedAddress.executes input tape width index base ao wo zo yo io bo savedOrigin hwidth s
      hready.zero hready.width hready.scratch hready.multiply hready.index hready.base hready.saved
  let address := (addressValue base + addressValue width * addressValue index).bits
  have ham : a.val.memory = s.val.memory := haf.2.2.1
  have ha6 : a.val.tapes 6 = BitTape.shifted clock clockOrigin :=
    (haf.2.2.2.2.2.1 6 (by omega) (by omega) (by omega)).trans h6
  have ha7 : a.val.tapes 7 = {BitTape.blank with head := outputOrigin} :=
    (haf.2.2.2.2.2.1 7 (by omega) (by omega) (by omega)).trans h7
  have hvalue : addressValue address = addressValue base + i.val * addressValue width := by
    simp [address, addressValue_bits, hindex, Nat.mul_comm]
  obtain ⟨rcost, r, finalAddress, hrcost, hr, hrpc, hr5, hrv, hrl, hr6, hr7, hrarray, hrf⟩ :=
    BitArray.read_steps input tape (addressValue base) (addressValue width) words i address clock
      addressOrigin clockOrigin outputOrigin a.val a.property (by simpa [ham] using harray)
      hvalue hclock ha5 ha6 ha7
  let t := Store.ofState r
  have rexec : Executes input tape (.call MemoryWord.readProgram) (rcost + 1) a t :=
    .call _ a r rcost hr (by rw [hrpc]; rfl)
  have hlen := address_length_le width index base
  have hrest : Restored t.val width base (yo + index.length) bo (savedOrigin + width.length) := by
    refine ⟨⟨ro, ?_⟩, ⟨widthOrigin, ?_⟩, ⟨so, ?_⟩, ?_, ?_, ?_⟩
    · exact (hrf.2.2.2.2.2.1 0 (by omega) (by omega) (by omega)).trans ha0
    · exact (hrf.2.2.2.2.2.1 1 (by omega) (by omega) (by omega)).trans ha1
    · exact (hrf.2.2.2.2.2.1 2 (by omega) (by omega) (by omega)).trans ha2
    · exact (hrf.2.2.2.2.2.1 3 (by omega) (by omega) (by omega)).trans ha3
    · exact (hrf.2.2.2.2.2.1 8 (by omega) (by omega) (by omega)).trans ha8
    · exact (hrf.2.2.2.2.2.1 9 (by omega) (by omega) (by omega)).trans ha9
  refine ⟨acost + (rcost + 1), t, finalAddress, addressOrigin, ?_, ha.seq rexec,
    hr5, hrv, by dsimp [address] at hrl; omega, hr6, hr7, hrf.2.1.trans ham,
    hrarray, hrest, (Frame.of_address haf).trans (Frame.of_read hrf)⟩
  dsimp [costCap]
  dsimp [address] at hrcost
  nlinarith

/-- The write path computes the same exact indexed address and realizes one
array update, preserving all neighboring entries and unrelated memory bits. -/
theorem write_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index base word : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (ao wo zo yo io bo savedOrigin sourceOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hword : word.length = addressValue width) (s : Store)
    (hready : Ready s.val width index base ao wo zo yo io bo savedOrigin)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words)
    (h6 : s.val.tapes 6 = BitTape.shifted word sourceOrigin) :
    ∃ cost t finalAddress addressOrigin,
      cost ≤ costCap width index base (addressValue width) ∧
      Executes input tape writeCode cost s t ∧
      t.val.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue base + (i.val + 1) * addressValue width ∧
      finalAddress.length ≤ width.length + index.length + base.length + 1 + addressValue width ∧
      t.val.tapes 6 = BitTape.shiftedEnd word sourceOrigin ∧
      t.val.memory = MemoryWord.writeBits s.val.memory
        (addressValue base + i.val * addressValue width) word ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width) (words.set i word) ∧
      Restored t.val width base (yo + index.length) bo (savedOrigin + width.length) ∧ Frame s.val t.val ∧ t.val.tapes 7 = s.val.tapes 7 := by
  obtain ⟨acost, a, ro, so, addressOrigin, widthOrigin, hacost, ha, ha0, ha1, ha2, ha3,
    ha5, ha8, ha9, haf⟩ :=
    IndexedAddress.executes input tape width index base ao wo zo yo io bo savedOrigin hwidth s
      hready.zero hready.width hready.scratch hready.multiply hready.index hready.base hready.saved
  let address := (addressValue base + addressValue width * addressValue index).bits
  have ham : a.val.memory = s.val.memory := haf.2.2.1
  have ha6 : a.val.tapes 6 = BitTape.shifted word sourceOrigin :=
    (haf.2.2.2.2.2.1 6 (by omega) (by omega) (by omega)).trans h6
  have hvalue : addressValue address = addressValue base + i.val * addressValue width := by
    simp [address, addressValue_bits, hindex, Nat.mul_comm]
  obtain ⟨rcost, r, finalAddress, hrcost, hr, hrpc, hr5, hrv, hrl, hr6, hrmem, hrarray, hrf⟩ :=
    BitArray.write_steps input tape (addressValue base) (addressValue width) words i address word
      addressOrigin sourceOrigin a.val a.property (by simpa [ham] using harray)
      hvalue hword ha5 ha6
  let t := Store.ofState r
  have rexec : Executes input tape (.call MemoryWord.writeProgram) (rcost + 1) a t :=
    .call _ a r rcost hr (by rw [hrpc]; rfl)
  have hlen := address_length_le width index base
  have hrest : Restored t.val width base (yo + index.length) bo (savedOrigin + width.length) := by
    refine ⟨⟨ro, ?_⟩, ⟨widthOrigin, ?_⟩, ⟨so, ?_⟩, ?_, ?_, ?_⟩
    · exact (hrf.2.2.2.2.1 0 (by omega) (by omega)).trans ha0
    · exact (hrf.2.2.2.2.1 1 (by omega) (by omega)).trans ha1
    · exact (hrf.2.2.2.2.1 2 (by omega) (by omega)).trans ha2
    · exact (hrf.2.2.2.2.1 3 (by omega) (by omega)).trans ha3
    · exact (hrf.2.2.2.2.1 8 (by omega) (by omega)).trans ha8
    · exact (hrf.2.2.2.2.1 9 (by omega) (by omega)).trans ha9
  refine ⟨acost + (rcost + 1), t, finalAddress, addressOrigin, ?_, ha.seq rexec,
    hr5, hrv, by dsimp [address] at hrl; omega, hr6,
    by simpa only [t, Store.ofState, ham] using hrmem,
    hrarray, hrest, (Frame.of_address haf).trans (Frame.of_write hrf),
    (hrf.2.2.2.2.1 7 (by omega) (by omega)).trans
      (haf.2.2.2.2.2.1 7 (by omega) (by omega) (by omega))⟩
  dsimp [costCap]
  dsimp [address] at hrcost
  nlinarith

/-- Capped finite-code read, including computed-address arithmetic. -/
theorem read_run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index base clock : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (ao wo zo yo io bo savedOrigin clockOrigin outputOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : BitRAMState) (hpc : s.pc = 0)
    (hready : Ready s width index base ao wo zo yo io bo savedOrigin)
    (harray : BitArray.Represents s.memory (addressValue base) (addressValue width) words)
    (h6 : s.tapes 6 = BitTape.shifted clock clockOrigin)
    (h7 : s.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ t finalAddress addressOrigin,
      (runPriced (readProgram.next input tape) (costCap width index base (addressValue width) + 1) s).finished = some t ∧
      (runPriced (readProgram.next input tape) (costCap width index base (addressValue width) + 1) s).instructions ≤
        costCap width index base (addressValue width) ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue base + (i.val + 1) * addressValue width ∧
      finalAddress.length ≤ width.length + index.length + base.length + 1 + addressValue width ∧
      t.tapes 6 = BitTape.shiftedEnd clock clockOrigin ∧
      t.tapes 7 = BitTape.shiftedEnd (words.get i) outputOrigin ∧
      t.memory = s.memory ∧
      BitArray.Represents t.memory (addressValue base) (addressValue width) words ∧
      Restored t width base (yo + index.length) bo (savedOrigin + width.length) ∧ Frame s t := by
  obtain ⟨cost, t, finalAddress, addressOrigin, hc, hs, ht5, hv, hl, ht6, ht7, hm, harr, hrest, hf⟩ :=
    read_executes input tape width index base clock words i ao wo zo yo io bo savedOrigin clockOrigin outputOrigin
      hwidth hindex hclock ⟨s, hpc⟩ hready harray h6 h7
  have hrun := hs.compiled_run (costCap width index base (addressValue width) + 1) (by omega)
  exact ⟨t.place readCode.size, finalAddress, addressOrigin, hrun.1, hrun.2.symm ▸ hc,
    ht5, hv, hl, ht6, ht7, hm, harr, hrest.place _, hf⟩

/-- Capped finite-code write, with the complete interval update retained. -/
theorem write_run {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index base word : List Bool) (words : Vector (List Bool) n) (i : Fin n)
    (ao wo zo yo io bo savedOrigin sourceOrigin : ℤ)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hword : word.length = addressValue width) (s : BitRAMState) (hpc : s.pc = 0)
    (hready : Ready s width index base ao wo zo yo io bo savedOrigin)
    (harray : BitArray.Represents s.memory (addressValue base) (addressValue width) words)
    (h6 : s.tapes 6 = BitTape.shifted word sourceOrigin) :
    ∃ t finalAddress addressOrigin,
      (runPriced (writeProgram.next input tape) (costCap width index base (addressValue width) + 1) s).finished = some t ∧
      (runPriced (writeProgram.next input tape) (costCap width index base (addressValue width) + 1) s).instructions ≤
        costCap width index base (addressValue width) ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue base + (i.val + 1) * addressValue width ∧
      finalAddress.length ≤ width.length + index.length + base.length + 1 + addressValue width ∧
      t.tapes 6 = BitTape.shiftedEnd word sourceOrigin ∧
      t.memory = MemoryWord.writeBits s.memory (addressValue base + i.val * addressValue width) word ∧
      BitArray.Represents t.memory (addressValue base) (addressValue width) (words.set i word) ∧
      Restored t width base (yo + index.length) bo (savedOrigin + width.length) ∧ Frame s t ∧ t.tapes 7 = s.tapes 7 := by
  obtain ⟨cost, t, finalAddress, addressOrigin, hc, hs, ht5, hv, hl, ht6, hm, harr, hrest, hf, hseven⟩ :=
    write_executes input tape width index base word words i ao wo zo yo io bo savedOrigin sourceOrigin
      hwidth hindex hword ⟨s, hpc⟩ hready harray h6
  have hrun := hs.compiled_run (costCap width index base (addressValue width) + 1) (by omega)
  exact ⟨t.place writeCode.size, finalAddress, addressOrigin, hrun.1, hrun.2.symm ▸ hc,
    ht5, hv, hl, ht6, hm, harr, hrest.place _, hf, hseven⟩

end Maxwell.Cost.ArrayAccess
