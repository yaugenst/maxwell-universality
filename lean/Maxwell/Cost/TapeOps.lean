import Maxwell.Cost.ParseNat

/-! Uniform tape loops executed by the concrete priced Boolean machine.
Their costs count interpreter transitions, including the two-bit tape read.
-/

namespace Maxwell.Cost

/-- A finite word placed at any integer tape location, blank elsewhere. -/
def BitTape.shifted (bits : List Bool) (offset : ℤ) : BitTape :=
  ⟨offset, fun p => if offset ≤ p then bits[(p - offset).toNat]? else none⟩

@[simp] theorem BitTape.shifted_zero (bits : List Bool) :
    BitTape.shifted bits 0 = BitTape.ofList bits := by
  simp [BitTape.shifted, BitTape.ofList]

@[simp] theorem BitTape.shifted_read (bits : List Bool) (offset : ℤ) :
    (BitTape.shifted bits offset).read = bits.head? := by
  simp [BitTape.shifted, BitTape.read, List.head?_eq_getElem?]

@[simp] theorem BitTape.shifted_nil (offset : ℤ) :
    BitTape.shifted [] offset = {BitTape.blank with head := offset} := by
  simp [BitTape.shifted, BitTape.blank]

theorem BitTape.shifted_erase_move (b : Bool) (bits : List Bool) (offset : ℤ) :
    {(BitTape.shifted (b :: bits) offset).write none with head := offset + 1} =
      BitTape.shifted bits (offset + 1) := by
  apply BitTape.ext <;> try rfl
  funext p
  simp only [BitTape.write, BitTape.shifted]
  by_cases heq : p = offset
  · subst p
    simp
  · rw [Function.update_of_ne heq]
    by_cases hp : offset ≤ p
    · have hp' : offset + 1 ≤ p := by omega
      have hi : (p - offset).toNat = (p - (offset + 1)).toNat + 1 := by omega
      simp [hp, hp', hi]
    · have hp' : ¬offset + 1 ≤ p := by omega
      simp [hp, hp']

/-- A word at an arbitrary origin, with the head just after its last bit. -/
def BitTape.shiftedEnd (bits : List Bool) (offset : ℤ) : BitTape :=
  {BitTape.shifted bits offset with head := offset + bits.length}

@[simp] theorem BitTape.shiftedEnd_zero (bits : List Bool) :
    BitTape.shiftedEnd bits 0 = BitTape.atEnd bits := by
  simp [BitTape.shiftedEnd, BitTape.atEnd]

@[simp] theorem BitTape.shiftedEnd_nil (offset : ℤ) :
    BitTape.shiftedEnd [] offset = {BitTape.blank with head := offset} := by
  simp [BitTape.shiftedEnd]

theorem BitTape.shiftedEnd_append_write (bits : List Bool) (offset : ℤ) (b : Bool) :
    {(BitTape.shiftedEnd bits offset).write (some b) with
      head := (BitTape.shiftedEnd bits offset).head + 1} =
      BitTape.shiftedEnd (bits ++ [b]) offset := by
  apply BitTape.ext
  · simp [BitTape.shiftedEnd, Nat.cast_add, add_assoc]
  · funext p
    simp only [BitTape.write, BitTape.shiftedEnd, BitTape.shifted]
    by_cases heq : p = offset + (bits.length : ℤ)
    · subst p
      simp
    · rw [Function.update_of_ne heq]
      by_cases hp : offset ≤ p
      · simp only [ite_eq_left hp]
        have hn : (p - offset).toNat ≠ bits.length := by omega
        by_cases hlt : (p - offset).toNat < bits.length
        · simp [List.getElem?_append, hlt]
        · have hgt : bits.length < (p - offset).toNat := by omega
          simp [List.getElem?_append, hlt,
            show (p - offset).toNat - bits.length ≠ 0 by omega]
      · simp [hp]

namespace TapeOps

/-- Copy to the destination and erase the source one symbol at a time.
Only the two tape identifiers are program parameters; word width is data. -/
def copyClear (source target : ℕ) : BitRAM := ⟨[
  .readTape source 26 27,
  .branch 27 2 7,
  .writeTape target 26,
  .eraseTape source,
  .tapeRight source,
  .tapeRight target,
  .jump 0,
  .halt]⟩

def copyClearNext (source target : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update s.registers 26 b) 27 true
    tapes := Function.update (Function.update s.tapes source
      {(s.tapes source).write none with head := (s.tapes source).head + 1}) target
      {(s.tapes target).write (some b) with head := (s.tapes target).head + 1}}

def copyClearExit (s : BitRAMState) : BitRAMState :=
  {s with pc := 7, registers := Function.update (Function.update s.registers 26 false) 27 false}

/-- The loop preserves every input, random, memory and output channel;
only its two tapes and scratch Boolean registers can change. -/
def Frame (source target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ source → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.refl (source target : ℕ) (s : BitRAMState) : Frame source target s s := by
  simp [Frame]

theorem Frame.trans {source target : ℕ} {s t u : BitRAMState}
    (h : Frame source target s t) (k : Frame source target t u) : Frame source target s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hs hd => (kt i hs hd).trans (ht i hs hd),
    fun i h26 h27 => (kg i h26 h27).trans (hg i h26 h27)⟩

theorem copyClear_next_frame (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : (copyClear source target).next input randomTape s = some step) :
    Frame source target s step.state := by
  have hlt : s.pc < 8 := by
    by_contra! hge
    have hnone : (copyClear source target).code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [copyClear] using hge)
    simp [BitRAM.next, hnone] at h
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, copyClear, hp] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape, Function.update_apply]
  all_goals intros; simp_all

theorem copyClear_steps_frame (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState}
    (h : PricedSteps ((copyClear source target).next input randomTape) cost s t) :
    Frame source target s t := by
  induction h with
  | refl s => exact Frame.refl source target s
  | step h rest ih => exact (copyClear_next_frame source target input randomTape h).trans ih

theorem copyClear_block (source target : ℕ) (hneq : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState) (b : Bool)
    (hpc : s.pc = 0) (hread : (s.tapes source).read = some b) :
    PricedSteps ((copyClear source target).next input randomTape) 8 s
      (copyClearNext source target s b) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions, BitRAM.next, copyClear, hpc, hread,
    BitRAMState.setRegister, BitRAMState.setTape, copyClearNext, BitTape.write,
    hneq, Ne.symm hneq, Function.update_comm hneq]

theorem copyClear_exit_block (source target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes source).read = none) :
    PricedSteps ((copyClear source target).next input randomTape) 3 s (copyClearExit s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, copyClear, hpc, hread,
    BitRAMState.setRegister, copyClearExit]

/-- Exact global tape contents and interpreter cost at independent source
and destination origins, including negative origins after word shifts. -/
theorem copyClear_shifted_steps (source target : ℕ) (hneq : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (bits preceding : List Bool)
    (offset destinationOffset : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes source = BitTape.shifted bits offset)
    (htarget : s.tapes target = BitTape.shiftedEnd preceding destinationOffset) :
    ∃ t, PricedSteps ((copyClear source target).next input randomTape)
        (8 * bits.length + 3) s t ∧ t.pc = 7 ∧
      t.tapes source = {BitTape.blank with head := offset + bits.length} ∧
      t.tapes target = BitTape.shiftedEnd (preceding ++ bits) destinationOffset ∧
      Frame source target s t := by
  induction bits generalizing preceding offset s with
  | nil =>
    have hread : (s.tapes source).read = none := by rw [hsource]; simp [BitTape.read, BitTape.blank]
    refine ⟨copyClearExit s, copyClear_exit_block source target input randomTape s hpc hread,
      rfl, ?_, ?_, ?_⟩
    · simpa [copyClearExit] using hsource
    · simpa [copyClearExit] using htarget
    · simp [Frame, copyClearExit]
      intros; simp_all
  | cons b bits ih =>
    have hread : (s.tapes source).read = some b := by rw [hsource]; simp
    have hstep := copyClear_block source target hneq input randomTape s b hpc hread
    have hnextsource : (copyClearNext source target s b).tapes source =
        BitTape.shifted bits (offset + 1) := by
      simp only [copyClearNext, Function.update_of_ne hneq, Function.update_self, hsource]
      exact BitTape.shifted_erase_move b bits offset
    have hnexttarget : (copyClearNext source target s b).tapes target =
        BitTape.shiftedEnd (preceding ++ [b]) destinationOffset := by
      simp only [copyClearNext, Function.update_self, htarget]
      exact BitTape.shiftedEnd_append_write preceding destinationOffset b
    obtain ⟨t, hrest, htpc, htsource, httarget, hframe⟩ :=
      ih (preceding ++ [b]) (offset + 1) (copyClearNext source target s b) rfl hnextsource hnexttarget
    refine ⟨t, ?_, htpc, ?_, ?_, (copyClear_steps_frame source target input randomTape hstep).trans hframe⟩
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hrest
    · simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
        add_comm, add_left_comm] using htsource
    · simpa [List.append_assoc] using httarget

/-- The original zero-origin destination contract is a specialization. -/
theorem copyClear_steps (source target : ℕ) (hneq : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (bits preceding : List Bool) (offset : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes source = BitTape.shifted bits offset)
    (htarget : s.tapes target = BitTape.atEnd preceding) :
    ∃ t, PricedSteps ((copyClear source target).next input randomTape)
        (8 * bits.length + 3) s t ∧ t.pc = 7 ∧
      t.tapes source = {BitTape.blank with head := offset + bits.length} ∧
      t.tapes target = BitTape.atEnd (preceding ++ bits) ∧ Frame source target s t := by
  simpa using copyClear_shifted_steps source target hneq input randomTape bits preceding offset 0
    s hpc hsource (by simpa using htarget)

/-- Clearing and transferring a shifted accumulator into a globally blank
tape works at any destination head, with no repositioning assumption. -/
theorem copyClear_to_blank_steps (source target : ℕ) (hneq : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (bits : List Bool)
    (sourceOffset destinationOffset : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes source = BitTape.shifted bits sourceOffset)
    (htarget : s.tapes target = {BitTape.blank with head := destinationOffset}) :
    ∃ t, PricedSteps ((copyClear source target).next input randomTape)
        (8 * bits.length + 3) s t ∧ t.pc = 7 ∧
      t.tapes source = {BitTape.blank with head := sourceOffset + bits.length} ∧
      t.tapes target = BitTape.shiftedEnd bits destinationOffset ∧ Frame source target s t := by
  simpa using copyClear_shifted_steps source target hneq input randomTape bits []
    sourceOffset destinationOffset s hpc hsource (by simpa using htarget)

/-- The ordinary runner returns the exact copied tapes and charges the
proved cost; the final halt inspection uses the additional unit of fuel. -/
theorem copyClear_run (source target : ℕ) (hneq : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (bits preceding : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes source = BitTape.ofList bits)
    (htarget : s.tapes target = BitTape.atEnd preceding) :
    ∃ t, (runPriced ((copyClear source target).next input randomTape)
        (8 * bits.length + 4) s).finished = some t ∧
      (runPriced ((copyClear source target).next input randomTape)
        (8 * bits.length + 4) s).instructions = 8 * bits.length + 3 ∧
      t.tapes source = {BitTape.blank with head := bits.length} ∧
      t.tapes target = BitTape.atEnd (preceding ++ bits) ∧ Frame source target s t := by
  obtain ⟨t, hsteps, htpc, hs, ht, hf⟩ := copyClear_steps source target hneq input randomTape
    bits preceding 0 s hpc (by simpa using hsource) htarget
  have hhalt : (copyClear source target).next input randomTape t = none := by
    simp [BitRAM.next, copyClear, htpc]
  have hr := hsteps.runPriced hhalt
  refine ⟨t, ?_, ?_, ?_, ht, hf⟩
  · simpa [Nat.add_assoc] using hr.1
  · simpa [Nat.add_assoc] using hr.2
  · simpa using hs

/-- Clear a finite word, preserving every other tape and all non-scratch
registers. The finite code is independent of the word length. -/
def clear (source : ℕ) : BitRAM := ⟨[
  .readTape source 26 27,
  .branch 27 2 5,
  .eraseTape source,
  .tapeRight source,
  .jump 0,
  .halt]⟩

def clearNext (source : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update s.registers 26 b) 27 true
    tapes := Function.update s.tapes source
      {(s.tapes source).write none with head := (s.tapes source).head + 1}}

def clearExit (s : BitRAMState) : BitRAMState :=
  {s with pc := 5, registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem clear_next_frame (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : (clear source).next input randomTape s = some step) : Frame source source s step.state := by
  have hlt : s.pc < 6 := by
    by_contra! hge
    have hnone : (clear source).code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [clear] using hge)
    simp [BitRAM.next, hnone] at h
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, clear, hp] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape, Function.update_apply]
  all_goals intros; simp_all

theorem clear_steps_frame (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState}
    (h : PricedSteps ((clear source).next input randomTape) cost s t) : Frame source source s t := by
  induction h with
  | refl s => exact Frame.refl source source s
  | step h rest ih => exact (clear_next_frame source input randomTape h).trans ih

theorem clear_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0) (hread : (s.tapes source).read = some b) :
    PricedSteps ((clear source).next input randomTape) 6 s (clearNext source s b) := by
  apply executeInstructions_sound (instructions := 5)
  simp [executeInstructions, BitRAM.next, clear, hpc, hread,
    BitRAMState.setRegister, BitRAMState.setTape, clearNext, BitTape.write]

theorem clear_exit_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes source).read = none) :
    PricedSteps ((clear source).next input randomTape) 3 s (clearExit s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, clear, hpc, hread,
    BitRAMState.setRegister, clearExit]

theorem clear_steps (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (offset : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.shifted bits offset) :
    ∃ t, PricedSteps ((clear source).next input randomTape) (6 * bits.length + 3) s t ∧
      t.pc = 5 ∧ t.tapes source = {BitTape.blank with head := offset + bits.length} ∧
      Frame source source s t := by
  induction bits generalizing offset s with
  | nil =>
    have hread : (s.tapes source).read = none := by rw [htape]; simp [BitTape.read, BitTape.blank]
    have hs := clear_exit_block source input randomTape s hpc hread
    refine ⟨clearExit s, hs, rfl, ?_, clear_steps_frame source input randomTape hs⟩
    simpa [clearExit] using htape
  | cons b bits ih =>
    have hread : (s.tapes source).read = some b := by rw [htape]; simp
    have hstep := clear_block source input randomTape s b hpc hread
    have hnext : (clearNext source s b).tapes source = BitTape.shifted bits (offset + 1) := by
      simp only [clearNext, Function.update_self, htape]
      exact BitTape.shifted_erase_move b bits offset
    obtain ⟨t, hrest, hp, ht, hf⟩ := ih (offset + 1) (clearNext source s b) rfl hnext
    refine ⟨t, ?_, hp, ?_, (clear_steps_frame source input randomTape hstep).trans hf⟩
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hrest
    · simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
        add_comm, add_left_comm] using ht

theorem clear_run (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (offset : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.shifted bits offset) :
    ∃ t, (runPriced ((clear source).next input randomTape)
        (6 * bits.length + 4) s).finished = some t ∧
      (runPriced ((clear source).next input randomTape)
        (6 * bits.length + 4) s).instructions = 6 * bits.length + 3 ∧
      t.tapes source = {BitTape.blank with head := offset + bits.length} ∧ Frame source source s t := by
  obtain ⟨t, hs, hp, ht, hf⟩ := clear_steps source input randomTape bits offset s hpc htape
  have hhalt : (clear source).next input randomTape t = none := by simp [BitRAM.next, clear, hp]
  have hr := hs.runPriced hhalt
  exact ⟨t, by simpa [Nat.add_assoc] using hr.1, by simpa [Nat.add_assoc] using hr.2, ht, hf⟩

/-- A little-endian word has no redundant high zero bits. The empty word
represents zero. -/
def CanonicalBits (bits : List Bool) : Prop :=
  bits = [] ∨ ∃ preceding, bits = preceding ++ [true]

theorem trailing_zero_decomposition (bits : List Bool) :
    ∃ core n, bits = core ++ List.replicate n false ∧ CanonicalBits core := by
  induction bits using List.reverseRecOn with
  | nil => exact ⟨[], 0, rfl, Or.inl rfl⟩
  | append_singleton bits b ih =>
    cases b with
    | false =>
      obtain ⟨core, n, hbits, hcore⟩ := ih
      refine ⟨core, n + 1, ?_, hcore⟩
      rw [hbits, List.replicate_succ']
      simp [List.append_assoc]
    | true => exact ⟨bits ++ [true], 0, by simp, Or.inr ⟨bits, rfl⟩⟩

theorem addressValue_append_zeros (bits : List Bool) (n : ℕ) :
    addressValue (bits ++ List.replicate n false) = addressValue bits := by
  induction bits with
  | nil =>
    simp only [List.nil_append, addressValue]
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, addressValue, ih]
  | cons b bits ih => simp [addressValue, ih]

/-- Remove redundant high zero bits, beginning with the head just after
the word. A blank and a stored false bit are tested separately. -/
def trim (source : ℕ) : BitRAM := ⟨[
  .tapeLeft source,
  .readTape source 26 27,
  .branch 27 3 7,
  .branch 26 7 4,
  .eraseTape source,
  .tapeLeft source,
  .jump 1,
  .tapeRight source,
  .halt]⟩

def trimStart (source : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 1
    tapes := Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head - 1}}

def trimNext (source : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 1
    registers := Function.update (Function.update s.registers 26 false) 27 true
    tapes := Function.update s.tapes source
      {(s.tapes source).write none with head := (s.tapes source).head - 1}}

def trimExit (source : ℕ) (s : BitRAMState) (present : Bool) : BitRAMState :=
  {s with
    pc := 8
    registers := Function.update (Function.update s.registers 26 present) 27 present
    tapes := Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + 1}}

theorem trim_next_frame (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : (trim source).next input randomTape s = some step) : Frame source source s step.state := by
  have hlt : s.pc < 9 := by
    by_contra! hge
    have hnone : (trim source).code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [trim] using hge)
    simp [BitRAM.next, hnone] at h
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, trim, hp] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape, Function.update_apply]
  all_goals intros; simp_all

theorem trim_steps_frame (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState}
    (h : PricedSteps ((trim source).next input randomTape) cost s t) : Frame source source s t := by
  induction h with
  | refl s => exact Frame.refl source source s
  | step h rest ih => exact (trim_next_frame source input randomTape h).trans ih

theorem trim_start_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    PricedSteps ((trim source).next input randomTape) 1 s (trimStart source s) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, trim, hpc, BitRAMState.setTape, trimStart]

theorem trim_zero_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (hread : (s.tapes source).read = some false) :
    PricedSteps ((trim source).next input randomTape) 7 s (trimNext source s) := by
  apply executeInstructions_sound (instructions := 6)
  simp [executeInstructions, BitRAM.next, trim, hpc, hread,
    BitRAMState.setRegister, BitRAMState.setTape, trimNext, BitTape.write]

theorem trim_true_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (hread : (s.tapes source).read = some true) :
    PricedSteps ((trim source).next input randomTape) 5 s (trimExit source s true) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, trim, hpc, hread,
    BitRAMState.setRegister, BitRAMState.setTape, trimExit]

theorem trim_blank_block (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (hread : (s.tapes source).read = none) :
    PricedSteps ((trim source).next input randomTape) 4 s (trimExit source s false) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, BitRAM.next, trim, hpc, hread,
    BitRAMState.setRegister, BitRAMState.setTape, trimExit]

theorem trim_loop (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (core : List Bool) (hcore : CanonicalBits core) (n : ℕ)
    (s : BitRAMState) (hpc : s.pc = 1)
    (htape : s.tapes source = BitTape.beforeEnd (core ++ List.replicate n false)) :
    ∃ cost t, cost ≤ 7 * n + 5 ∧
      PricedSteps ((trim source).next input randomTape) cost s t ∧
      t.pc = 8 ∧ t.tapes source = BitTape.atEnd core := by
  induction n generalizing s with
  | zero =>
    simp only [List.replicate_zero, List.append_nil] at htape
    rcases hcore with rfl | ⟨preceding, rfl⟩
    · have hread : (s.tapes source).read = none := by
        rw [htape]; exact BitTape.beforeEnd_nil_read
      refine ⟨4, trimExit source s false, by omega,
        trim_blank_block source input randomTape s hpc hread, rfl, ?_⟩
      simp [trimExit, htape, BitTape.beforeEnd, BitTape.atEnd]
    · have hread : (s.tapes source).read = some true := by
        rw [htape]; exact BitTape.beforeEnd_read preceding true
      refine ⟨5, trimExit source s true, by omega,
        trim_true_block source input randomTape s hpc hread, rfl, ?_⟩
      simp [trimExit, htape, BitTape.beforeEnd, BitTape.atEnd]
  | succ n ih =>
    have hword : core ++ List.replicate (n + 1) false =
        (core ++ List.replicate n false) ++ [false] := by
      rw [List.replicate_succ']
      simp [List.append_assoc]
    have hread : (s.tapes source).read = some false := by
      rw [htape, hword]
      exact BitTape.beforeEnd_read _ false
    have hstep := trim_zero_block source input randomTape s hpc hread
    have hnext : (trimNext source s).tapes source =
        BitTape.beforeEnd (core ++ List.replicate n false) := by
      simp only [trimNext, Function.update_self, htape, hword]
      exact BitTape.erase_last _ false
    obtain ⟨cost, t, hc, hs, hp, ht⟩ := ih (trimNext source s) rfl hnext
    exact ⟨7 + cost, t, by omega, hstep.trans hs, hp, ht⟩

/-- Uniform, finite-program normalization on every finite input word,
with exact output cells and a derived linear bit-operation bound. -/
theorem trim_steps (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.atEnd bits) :
    ∃ cost t core, cost ≤ 7 * bits.length + 6 ∧
      PricedSteps ((trim source).next input randomTape) cost s t ∧
      t.pc = 8 ∧ t.tapes source = BitTape.atEnd core ∧
      CanonicalBits core ∧ addressValue core = addressValue bits ∧
      core.length ≤ bits.length ∧ Frame source source s t := by
  obtain ⟨core, n, hbits, hcore⟩ := trailing_zero_decomposition bits
  have hstart := trim_start_block source input randomTape s hpc
  have ht : (trimStart source s).tapes source =
      BitTape.beforeEnd (core ++ List.replicate n false) := by
    simp [trimStart, htape, hbits, BitTape.atEnd, BitTape.beforeEnd]
  obtain ⟨cost, t, hc, hsteps, hp, hout⟩ :=
    trim_loop source input randomTape core hcore n (trimStart source s) rfl ht
  have hlen : bits.length = core.length + n := by simp [hbits]
  have hall := hstart.trans hsteps
  refine ⟨1 + cost, t, core, by omega, hall, hp, hout, hcore, ?_, by omega,
    trim_steps_frame source input randomTape hall⟩
  rw [hbits, addressValue_append_zeros]

theorem trim_run (source : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.atEnd bits) :
    ∃ t core, (runPriced ((trim source).next input randomTape)
        (7 * bits.length + 7) s).finished = some t ∧
      (runPriced ((trim source).next input randomTape)
        (7 * bits.length + 7) s).instructions ≤ 7 * bits.length + 6 ∧
      t.tapes source = BitTape.atEnd core ∧ CanonicalBits core ∧
      addressValue core = addressValue bits ∧ core.length ≤ bits.length ∧ Frame source source s t := by
  obtain ⟨cost, t, core, hc, hs, hp, ht, hcore, hvalue, hlen, hf⟩ :=
    trim_steps source input randomTape bits s hpc htape
  have hhalt : (trim source).next input randomTape t = none := by simp [BitRAM.next, trim, hp]
  have hr := hs.runPriced_ge hhalt (7 * bits.length + 7) (by omega)
  exact ⟨t, core, hr.1, hr.2 ▸ hc, ht, hcore, hvalue, hlen, hf⟩

end TapeOps

end Maxwell.Cost
