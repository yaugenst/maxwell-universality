import Maxwell.Cost.Execution
import Maxwell.Codec

/-! A finite, uniform sequential program for the self-delimiting natural
number codec. The output is its little-endian bit string on tape 11. -/

namespace Maxwell.Cost

theorem BitTape.ext {s t : BitTape} (hh : s.head = t.head) (hc : s.cells = t.cells) :
    s = t := by
  cases s
  cases t
  cases hh
  cases hc
  rfl

def BitTape.ofList (bits : List Bool) : BitTape :=
  ⟨0, fun p => if 0 ≤ p then bits[p.toNat]? else none⟩

def BitTape.Represents (tape : BitTape) (bits : List Bool) : Prop :=
  ∀ k : ℕ, tape.cells (tape.head + k) = bits[k]?

def BitTape.atEnd (bits : List Bool) : BitTape :=
  {BitTape.ofList bits with head := bits.length}

def BitTape.beforeEnd (bits : List Bool) : BitTape :=
  {BitTape.ofList bits with head := (bits.length : ℤ) - 1}

theorem BitTape.ofList_represents (bits : List Bool) :
    (BitTape.ofList bits).Represents bits := by
  intro k
  simp [BitTape.ofList]

theorem BitTape.atEnd_nil : BitTape.atEnd [] = BitTape.blank := by
  simp [BitTape.atEnd, BitTape.ofList, BitTape.blank]

theorem BitTape.append_write (bits : List Bool) (b : Bool) :
    {(BitTape.atEnd bits).write (some b) with
      head := (BitTape.atEnd bits).head + 1} = BitTape.atEnd (bits ++ [b]) := by
  apply BitTape.ext
  · simp [BitTape.atEnd, BitTape.ofList]
  · funext p
    simp only [BitTape.write, BitTape.atEnd, BitTape.ofList]
    by_cases heq : p = (bits.length : ℤ)
    · subst p
      simp
    · rw [Function.update_of_ne heq]
      by_cases hp : 0 ≤ p
      · simp only [ite_eq_left hp]
        have hn : p.toNat ≠ bits.length := by omega
        by_cases hlt : p.toNat < bits.length
        · simp [List.getElem?_append, hlt]
        · have hgt : bits.length < p.toNat := by omega
          simp [List.getElem?_append, hlt,
            show p.toNat - bits.length ≠ 0 by omega]
      · simp [hp]

theorem BitTape.beforeEnd_read (bits : List Bool) (b : Bool) :
    (BitTape.beforeEnd (bits ++ [b])).read = some b := by
  simp [BitTape.beforeEnd, BitTape.ofList, BitTape.read]

theorem BitTape.beforeEnd_nil_read : (BitTape.beforeEnd []).read = none := by
  simp [BitTape.beforeEnd, BitTape.ofList, BitTape.read]

theorem BitTape.erase_last (bits : List Bool) (b : Bool) :
    {(BitTape.beforeEnd (bits ++ [b])).write none with
      head := (BitTape.beforeEnd (bits ++ [b])).head - 1} = BitTape.beforeEnd bits := by
  apply BitTape.ext
  · simp [BitTape.beforeEnd, BitTape.ofList]
  · funext p
    simp only [BitTape.write, BitTape.beforeEnd, BitTape.ofList,
      List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right]
    by_cases heq : p = (bits.length : ℤ)
    · subst p
      simp
    · rw [Function.update_of_ne heq]
      by_cases hp : 0 ≤ p
      · simp only [ite_eq_left hp]
        have hn : p.toNat ≠ bits.length := by omega
        by_cases hlt : p.toNat < bits.length
        · simp [List.getElem?_append, hlt]
        · have hgt : bits.length < p.toNat := by omega
          simp [List.getElem?_append, hlt,
            show p.toNat - bits.length ≠ 0 by omega]
      · simp [hp]

namespace ParseNat

def program : BitRAM := ⟨[
  .readSequential 20, .branch 20 2 7, .literal 21 true,
  .writeTape 10 21, .tapeRight 10, .inputRight, .jump 0,
  .inputRight, .tapeLeft 10,
  .readTape 10 20 22, .branch 22 11 18,
  .readSequential 20, .writeTape 11 20, .tapeRight 11, .inputRight,
  .eraseTape 10, .tapeLeft 10, .jump 9, .halt]⟩

def headerNext (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update s.registers 20 true) 21 true
    inputHead := s.inputHead + 1
    tapes := Function.update s.tapes 10
      {(s.tapes 10).write (some true) with head := (s.tapes 10).head + 1}}

def headerExit (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 9
    registers := Function.update s.registers 20 false
    inputHead := s.inputHead + 1
    tapes := Function.update s.tapes 10
      {s.tapes 10 with head := (s.tapes 10).head - 1}}

def payloadNext (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 9
    registers := Function.update
      (Function.update (Function.update s.registers 20 true) 22 true) 20 b
    inputHead := s.inputHead + 1
    tapes := Function.update (Function.update s.tapes 11
      {(s.tapes 11).write (some b) with head := (s.tapes 11).head + 1}) 10
      {(s.tapes 10).write none with head := (s.tapes 10).head - 1}}

def payloadExit (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 18
    registers := Function.update (Function.update s.registers 20 false) 22 false}

/-- The parser reserves only tapes 10/11 and registers 20/21/22. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 11 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) :
    Frame s u := by
  rcases h with ⟨ha, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h10 h11 => (kt i h10 h11).trans (ht i h10 h11),
    fun i h20 h21 h22 => (kg i h20 h21 h22).trans (hg i h20 h21 h22)⟩

theorem next_frame (input : List Bool) (randomTape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : program.next input randomTape s = some step) : Frame s step.state := by
  have hlt : s.pc < 19 := by
    by_contra! hge
    have hnone : program.code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [program] using hge)
    simp [BitRAM.next, hnone] at h
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, program, hp] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape,
    Function.update_apply]
  all_goals intros; simp_all

theorem pricedSteps_frame (input : List Bool) (randomTape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState}
    (h : PricedSteps (program.next input randomTape) cost s t) : Frame s t := by
  induction h with
  | refl s => exact Frame.refl s
  | step h rest ih => exact (next_frame input randomTape h).trans ih

theorem header_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hb : inputBit input s.inputHead = true) :
    PricedSteps (program.next input randomTape) 7 s (headerNext s) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions, BitRAM.next, program, hpc, hb,
    BitRAMState.setRegister, BitRAMState.setTape, headerNext, BitTape.write]

theorem header_exit_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hb : inputBit input s.inputHead = false) :
    PricedSteps (program.next input randomTape) 4 s (headerExit s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc, hb,
    BitRAMState.setRegister, BitRAMState.setTape, headerExit]

theorem payload_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 9)
    (hr : (s.tapes 10).read = some true) (hb : inputBit input s.inputHead = b) :
    PricedSteps (program.next input randomTape) 10 s (payloadNext s b) := by
  apply executeInstructions_sound (instructions := 9)
  simp [executeInstructions, BitRAM.next, program, hpc, hb, hr,
    BitRAMState.setRegister, BitRAMState.setTape, payloadNext, BitTape.write]

theorem payload_exit_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 9) (hr : (s.tapes 10).read = none) :
    PricedSteps (program.next input randomTape) 3 s (payloadExit s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hr,
    BitRAMState.setRegister, payloadExit]

theorem header_loop_from (input : List Bool) (randomTape : ℕ → Bool) (length : ℕ)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hiout : initial.tapes 11 = BitTape.blank)
    (hb : ∀ k < length, inputBit input (initial.inputHead + k) = true) :
    ∃ s : BitRAMState,
      PricedSteps (program.next input randomTape) (7 * length) initial s ∧
      s.pc = 0 ∧ s.inputHead = initial.inputHead + length ∧
      s.tapes 10 = BitTape.atEnd (List.replicate length true) ∧
      s.tapes 11 = BitTape.blank := by
  induction length with
  | zero =>
    refine ⟨initial, ?_, hipc, ?_, ?_, hiout⟩
    · simpa using PricedSteps.refl (next := program.next input randomTape) initial
    · simp
    · simpa [BitTape.atEnd_nil] using hicount
  | succ length ih =>
    obtain ⟨s, hs, hpc, hh, ht, ho⟩ := ih (fun k hk => hb k (by omega))
    have hstep := header_block input randomTape s hpc (by rw [hh]; exact hb length (by omega))
    refine ⟨headerNext s, ?_, rfl, ?_, ?_, ?_⟩
    · convert hs.trans hstep using 1
    · simp [headerNext, hh, add_assoc]
    · simp only [headerNext, Function.update_self, ht]
      rw [BitTape.append_write, ← List.replicate_succ']
    · simpa [headerNext] using ho

theorem header_loop (input : List Bool) (randomTape : ℕ → Bool) (length : ℕ)
    (hb : ∀ k < length, inputBit input k = true) :
    ∃ s : BitRAMState,
      PricedSteps (program.next input randomTape) (7 * length) BitRAMState.initial s ∧
      s.pc = 0 ∧ s.inputHead = length ∧
      s.tapes 10 = BitTape.atEnd (List.replicate length true) ∧
      s.tapes 11 = BitTape.blank := by
  simpa [BitRAMState.initial] using
    header_loop_from input randomTape length BitRAMState.initial rfl rfl rfl
      (by simpa [BitRAMState.initial] using hb)

theorem payload_loop (input : List Bool) (randomTape : ℕ → Bool)
    (remaining preceding : List Bool) (s : BitRAMState)
    (hpc : s.pc = 9)
    (ht : s.tapes 10 = BitTape.beforeEnd (List.replicate remaining.length true))
    (ho : s.tapes 11 = BitTape.atEnd preceding)
    (hb : ∀ k < remaining.length,
      inputBit input (s.inputHead + k) = remaining[k]?.getD false) :
    ∃ t : BitRAMState,
      PricedSteps (program.next input randomTape) (10 * remaining.length + 3) s t ∧
      t.pc = 18 ∧ t.inputHead = s.inputHead + remaining.length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧
      t.tapes 11 = BitTape.atEnd (preceding ++ remaining) := by
  induction remaining generalizing preceding s with
  | nil =>
    have hread : (s.tapes 10).read = none := by
      rw [ht]
      exact BitTape.beforeEnd_nil_read
    refine ⟨payloadExit s, payload_exit_block input randomTape s hpc hread,
      rfl, ?_, ?_, ?_⟩
    · simp [payloadExit]
    · simpa [payloadExit] using ht
    · simpa [payloadExit] using ho
  | cons b bs ih =>
    have hread : (s.tapes 10).read = some true := by
      rw [ht, List.length_cons, List.replicate_succ']
      exact BitTape.beforeEnd_read _ _
    have hbit : inputBit input s.inputHead = b := by simpa using hb 0 (by simp)
    have hstep := payload_block input randomTape s b hpc hread hbit
    have hnextTape : (payloadNext s b).tapes 10 =
        BitTape.beforeEnd (List.replicate bs.length true) := by
      simp only [payloadNext, Function.update_self, ht, List.length_cons]
      rw [List.replicate_succ', BitTape.erase_last]
    have hnextOut : (payloadNext s b).tapes 11 = BitTape.atEnd (preceding ++ [b]) := by
      simp only [payloadNext, Function.update_of_ne (by decide : (11 : ℕ) ≠ 10),
        Function.update_self, ho]
      exact BitTape.append_write _ _
    have hnextBits : ∀ k < bs.length,
        inputBit input ((payloadNext s b).inputHead + k) = bs[k]?.getD false := by
      intro k hk
      have hh := hb (k + 1) (by simp; omega)
      simpa [payloadNext, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hh
    obtain ⟨t, hexec, htpc, hthead, httape, htout⟩ :=
      ih (preceding ++ [b]) (payloadNext s b) rfl hnextTape hnextOut hnextBits
    refine ⟨t, ?_, htpc, ?_, httape, ?_⟩
    · convert hstep.trans hexec using 1
      simp
      omega
    · simpa [payloadNext, List.length_cons, Nat.cast_add, add_assoc,
        add_comm, add_left_comm] using hthead
    · simpa [List.append_assoc] using htout

theorem inputBit_append_offset (preceding bits : List Bool) (k : ℕ) :
    inputBit (preceding ++ bits) (preceding.length + k) = bits[k]?.getD false := by
  have hnonneg : ¬ (preceding.length : ℤ) + k < 0 := by omega
  have hnat : ((preceding.length : ℤ) + k).toNat = preceding.length + k := by omega
  simp [inputBit, hnonneg, hnat, List.getElem?_append,
    show ¬ preceding.length + k < preceding.length by omega]

/-- A composable parser segment after an arbitrary input prefix. All
unreserved machine data is preserved, including the random-tape cursor. -/
theorem parse_bits_steps (bits preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hihead : initial.inputHead = preceding.length)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hiout : initial.tapes 11 = BitTape.blank) :
    ∃ t : BitRAMState,
      PricedSteps (program.next
        (preceding ++ ((List.replicate bits.length true ++ false :: bits) ++ suffix)) randomTape)
        (17 * bits.length + 7) initial t ∧
      t.pc = 18 ∧ t.inputHead = initial.inputHead + 2 * (bits.length : ℤ) + 1 ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd bits ∧ Frame initial t := by
  let input := preceding ++ ((List.replicate bits.length true ++ false :: bits) ++ suffix)
  have hheader : ∀ k < bits.length, inputBit input (initial.inputHead + k) = true := by
    intro k hk
    rw [hihead]
    change inputBit (preceding ++ _) _ = _
    rw [inputBit_append_offset]
    simp [List.getElem?_append, hk]
  obtain ⟨s, hsteps, hpc, hhead, htape, hout⟩ :=
    header_loop_from input randomTape bits.length initial hipc hicount hiout hheader
  have hzero : inputBit input s.inputHead = false := by
    rw [hhead, hihead]
    change inputBit (preceding ++ _) _ = _
    rw [inputBit_append_offset]
    simp
  have hexit := header_exit_block input randomTape s hpc hzero
  have htape' : (headerExit s).tapes 10 =
      BitTape.beforeEnd (List.replicate bits.length true) := by
    simp only [headerExit, Function.update_self, htape]
    rfl
  have hout' : (headerExit s).tapes 11 = BitTape.atEnd [] := by
    simpa [headerExit, BitTape.atEnd_nil] using hout
  have hbits : ∀ k < bits.length,
      inputBit input ((headerExit s).inputHead + k) = bits[k]?.getD false := by
    intro k hk
    have heq : input =
        (preceding ++ (List.replicate bits.length true ++ [false])) ++ (bits ++ suffix) := by
      simp [input, List.append_assoc]
    rw [heq]
    have hh : (headerExit s).inputHead + k =
        ((preceding ++ (List.replicate bits.length true ++ [false])).length : ℤ) + k := by
      simp [headerExit, hhead, hihead, add_assoc]
    rw [hh, inputBit_append_offset, List.getElem?_append_left hk]
  obtain ⟨t, hpayload, htpc, hthead, httape, htout⟩ :=
    payload_loop input randomTape bits [] (headerExit s) rfl htape' hout' hbits
  have hall : PricedSteps (program.next input randomTape) (17 * bits.length + 7) initial t := by
    convert (hsteps.trans hexit).trans hpayload using 1
    omega
  refine ⟨t, hall, htpc, ?_, httape, ?_, pricedSteps_frame input randomTape hall⟩
  · simp only [headerExit, hhead] at hthead
    omega
  · simpa using htout

theorem parse_nat_steps (n : ℕ) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hihead : initial.inputHead = preceding.length)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hiout : initial.tapes 11 = BitTape.blank) :
    ∃ t : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.nat n ++ suffix)) randomTape)
        (17 * n.bits.length + 7) initial t ∧
      t.pc = 18 ∧ t.inputHead = initial.inputHead + (Codec.nat n).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd n.bits ∧ Frame initial t := by
  obtain ⟨t, hs, hp, hh, ht, ho, hf⟩ :=
    parse_bits_steps n.bits preceding suffix randomTape initial hipc hihead hicount hiout
  refine ⟨t, hs, hp, ?_, ht, ho, hf⟩
  simpa [Codec.nat, Nat.cast_add, two_mul, add_assoc, add_comm, add_left_comm] using hh

/-- Every finite payload is copied by the same nineteen-instruction program.
The suffix is never consumed. Its final tape head follows the payload. -/
theorem run_bits (bits suffix : List Bool) (randomTape : ℕ → Bool) :
    ∃ t : BitRAMState,
      (program.run ((List.replicate bits.length true ++ false :: bits) ++ suffix)
        randomTape (17 * bits.length + 8)).finished = some t ∧
      (program.run ((List.replicate bits.length true ++ false :: bits) ++ suffix)
        randomTape (17 * bits.length + 8)).instructions = 17 * bits.length + 7 ∧
      t.pc = 18 ∧ t.inputHead = 2 * (bits.length : ℤ) + 1 ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd bits := by
  let input := (List.replicate bits.length true ++ false :: bits) ++ suffix
  obtain ⟨t, hall, htpc, hthead, httape, htout, _⟩ :=
    parse_bits_steps bits [] suffix randomTape BitRAMState.initial rfl rfl rfl rfl
  have hhalt : program.next input randomTape t = none := by
    simp [BitRAM.next, program, htpc]
  obtain ⟨hfinish, hcost⟩ := hall.runPriced hhalt
  refine ⟨t, hfinish, hcost, htpc, ?_, httape, htout⟩
  simpa [BitRAMState.initial] using hthead

/-- Uniform finite-program parser for the actual natural-number codec,
with every interpreter operation charged and an arbitrary unread suffix. -/
theorem run_nat (n : ℕ) (suffix : List Bool) (randomTape : ℕ → Bool) :
    ∃ t : BitRAMState,
      (program.run (Codec.nat n ++ suffix) randomTape (17 * n.bits.length + 8)).finished = some t ∧
      (program.run (Codec.nat n ++ suffix) randomTape (17 * n.bits.length + 8)).instructions =
        17 * n.bits.length + 7 ∧
      t.pc = 18 ∧ t.inputHead = (Codec.nat n).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd n.bits := by
  obtain ⟨t, hf, hc, hp, hh, ht, ho⟩ := run_bits n.bits suffix randomTape
  refine ⟨t, hf, hc, hp, ?_, ht, ho⟩
  simpa [Codec.nat, Nat.cast_add, two_mul, add_assoc, add_comm, add_left_comm] using hh

end ParseNat
end Maxwell.Cost
