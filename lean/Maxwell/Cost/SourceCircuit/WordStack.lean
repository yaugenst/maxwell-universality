import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.NormalizeCoefficient.PadReverse.Tapes
import Maxwell.Cost.TapeReset
import Maxwell.Cost.WordTransfer

/-! A fixed finite pop consumes one clock symbol per stored bit. The stack
suffix is erased backwards and copied to a blank destination without
changing its bit order. -/

namespace Maxwell.Cost.SourceCircuit.WordStack
open Structured

def rawProgram (source clock target : ℕ) : BitRAM := ⟨[
  .readTape clock 26 27, .branch 27 2 9,
  .tapeLeft source, .tapeLeft target, .readTape source 28 29,
  .writeTape target 28, .eraseTape source, .tapeRight clock, .jump 0, .halt]⟩

def advanced (source clock target : ℕ) (s : BitRAMState) (clockBit bit : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update (Function.update
      (Function.update s.registers 26 clockBit) 27 true) 28 bit) 29 true
    tapes := Function.update (Function.update (Function.update s.tapes
      source ⟨(s.tapes source).head - 1,
        Function.update (s.tapes source).cells ((s.tapes source).head - 1) none⟩)
      target (({s.tapes target with head := (s.tapes target).head - 1}).write (some bit)))
      clock {s.tapes clock with head := (s.tapes clock).head + 1}}

def stopped (s : BitRAMState) : BitRAMState :=
  {s with pc := 9, registers := Function.update (Function.update s.registers 26 false) 27 false}

def LoopFrame (source clock target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
    t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
    (∀ j, j ≠ source → j ≠ clock → j ≠ target → t.tapes j = s.tapes j) ∧
    (∀ j, j ≠ 26 → j ≠ 27 → j ≠ 28 → j ≠ 29 → t.registers j = s.registers j)

theorem LoopFrame.trans {source clock target : ℕ} {s t u : BitRAMState}
    (h : LoopFrame source clock target s t) (k : LoopFrame source clock target t u) :
    LoopFrame source clock target s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun j hs hc ht => (k.2.2.2.2.2.1 j hs hc ht).trans (h.2.2.2.2.2.1 j hs hc ht),
    fun j h26 h27 h28 h29 =>
      (k.2.2.2.2.2.2 j h26 h27 h28 h29).trans (h.2.2.2.2.2.2 j h26 h27 h28 h29)⟩

theorem advanced_frame (source clock target : ℕ) (s : BitRAMState) (c b : Bool) :
    LoopFrame source clock target s (advanced source clock target s c b) := by
  simp [LoopFrame, advanced]
  constructor <;> intros <;> simp_all

theorem stopped_frame (source clock target : ℕ) (s : BitRAMState) :
    LoopFrame source clock target s (stopped s) := by
  simp [LoopFrame, stopped]
  intros; simp_all

theorem cycle (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (c b : Bool)
    (hpc : s.pc = 0) (hc : (s.tapes clock).read = some c)
    (hs : (s.tapes source).cells ((s.tapes source).head - 1) = some b) :
    PricedSteps ((rawProgram source clock target).next input tape) 11 s
      (advanced source clock target s c b) := by
  change (s.tapes clock).cells (s.tapes clock).head = some c at hc
  apply executeInstructions_sound (instructions := 9)
  simp [executeInstructions, rawProgram, BitRAM.next, hpc, hc, hs, advanced,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, BitTape.write,
    hst, hct, Ne.symm hsc, Ne.symm hst]
  funext j
  by_cases hj : j = source <;> by_cases hk : j = target <;>
    by_cases hl : j = clock <;> simp_all

theorem finish (source clock target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hc : (s.tapes clock).read = none) :
    PricedSteps ((rawProgram source clock target).next input tape) 3 s (stopped s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, rawProgram, BitRAM.next, hpc, hc, stopped, BitRAMState.setRegister]

theorem advanced_source (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (s : BitRAMState) (c b : Bool) (bits : List Bool)
    (hs : s.tapes source = BitTape.atEnd (bits ++ [b])) :
    (advanced source clock target s c b).tapes source = BitTape.atEnd bits := by
  simpa only [advanced, TapeReset.retreat, Function.update_of_ne hsc,
    Function.update_of_ne hst, Function.update_self] using
      TapeReset.retreat_tape source s bits b hs

theorem advanced_target (source clock target : ℕ) (hct : clock ≠ target)
    (s : BitRAMState) (c b : Bool) (bits : List Bool) (origin : ℤ)
    (ht : s.tapes target = BitTape.shifted bits origin) :
    (advanced source clock target s c b).tapes target =
      BitTape.shifted (b :: bits) (origin - 1) := by
  simp only [advanced, Function.update_of_ne (Ne.symm hct), Function.update_self, ht]
  exact NormalizeCoefficient.PadReverse.prepend_word bits origin b

set_option maxRecDepth 4096 in
theorem loop (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word lower preceding : List Bool)
    (targetOrigin clockOrigin : ℤ) (clockCells : ℤ → Option Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.atEnd (lower ++ word))
    (ht : s.tapes target = BitTape.shifted preceding targetOrigin)
    (hc : s.tapes clock = ⟨clockOrigin, clockCells⟩)
    (hp : ∀ k : ℕ, k < word.length → ∃ b, clockCells (clockOrigin + k) = some b)
    (he : clockCells (clockOrigin + word.length) = none) :
    ∃ t, PricedSteps ((rawProgram source clock target).next input tape)
      (11 * word.length + 3) s t ∧ t.pc = 9 ∧
      t.tapes source = BitTape.atEnd lower ∧
      t.tapes target = BitTape.shifted (word ++ preceding) (targetOrigin - word.length) ∧
      t.tapes clock = ⟨clockOrigin + word.length, clockCells⟩ ∧
      LoopFrame source clock target s t := by
  induction word using List.reverseRecOn generalizing preceding targetOrigin clockOrigin s with
  | nil =>
    refine ⟨stopped s, finish source clock target input tape s hpc ?_, rfl, ?_, ?_, ?_,
      stopped_frame source clock target s⟩
    · simpa [hc, BitTape.read] using he
    · simpa [stopped] using hs
    · simpa [stopped] using ht
    · simpa [stopped] using hc
  | append_singleton word b ih =>
    obtain ⟨c, hread⟩ := hp 0 (by simp)
    have readClock : (s.tapes clock).read = some c := by simpa [hc, BitTape.read] using hread
    have stack : s.tapes source = BitTape.atEnd ((lower ++ word) ++ [b]) := by
      simpa [List.append_assoc] using hs
    have readStack : (s.tapes source).cells ((s.tapes source).head - 1) = some b := by
      rw [stack]
      simpa [BitTape.beforeEnd, BitTape.atEnd, BitTape.read] using
        BitTape.beforeEnd_read (lower ++ word) b
    have step := cycle source clock target hsc hst hct input tape s c b hpc readClock readStack
    have nextClock : (advanced source clock target s c b).tapes clock =
        ⟨clockOrigin + 1, clockCells⟩ := by simp [advanced, hc]
    have present : ∀ k : ℕ, k < word.length → ∃ b, clockCells (clockOrigin + 1 + k) = some b := by
      intro k hk
      obtain ⟨v,hv⟩ := hp (k+1) (by simpa using hk)
      refine ⟨v, ?_⟩
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hv
    have ended : clockCells (clockOrigin + 1 + word.length) = none := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using he
    obtain ⟨t, steps, pc, sourceDone, targetDone, clockDone, frame⟩ := ih (b :: preceding)
      (targetOrigin-1) (clockOrigin+1) (advanced source clock target s c b) rfl
      (advanced_source source clock target hsc hst s c b (lower ++ word) stack)
      (advanced_target source clock target hct s c b preceding targetOrigin ht)
      nextClock present ended
    refine ⟨t, ?_, pc, sourceDone, ?_, ?_, (advanced_frame source clock target s c b).trans frame⟩
    · convert step.trans steps using 1
      simp
      omega
    · have ho : targetOrigin - 1 - (word.length : ℤ) =
          targetOrigin - ((word ++ [b]).length : ℤ) := by simp; omega
      rw [ho] at targetDone
      simpa only [List.append_assoc, List.singleton_append] using targetDone
    · simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using clockDone

def code (source clock target : ℕ) : Code :=
  .seq (.call (rawProgram source clock target)) (.call (Rewind.program clock))

def program (source clock target : ℕ) : BitRAM := (code source clock target).compile

set_option maxRecDepth 4096 in
/-- Pop a word whose width is the length of the physical clock. Both the
stack prefix and complete clock are preserved; no data determines code. -/
theorem executes (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word lower clockWord : List Bool)
    (targetOrigin clockOrigin : ℤ) (s : Store)
    (hwidth : clockWord.length = word.length)
    (hs : s.val.tapes source = BitTape.atEnd (lower ++ word))
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin})
    (hc : s.val.tapes clock = BitTape.shifted clockWord clockOrigin) :
    ∃ t : Store, Executes input tape (code source clock target) (15 * word.length + 10) s t ∧
      t.val.tapes source = BitTape.atEnd lower ∧
      t.val.tapes target = BitTape.shifted word (targetOrigin - word.length) ∧
      t.val.tapes clock = s.val.tapes clock ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame {source, target} s.val t.val ∧
      (∀ j, j ≠ source → j ≠ target → t.val.tapes j = s.val.tapes j) := by
  let cells := (BitTape.shifted clockWord clockOrigin).cells
  have present : ∀ k : ℕ, k < word.length → ∃ b, cells (clockOrigin + k) = some b := by
    intro k hk
    have hk' : k < clockWord.length := by omega
    exact ⟨clockWord[k], by simp [cells, BitTape.shifted, hk']⟩
  have ended : cells (clockOrigin + word.length) = none := by
    simp [cells, BitTape.shifted, ← hwidth]
  obtain ⟨r, er, rpc, rs, rt, rc, rf⟩ := loop source clock target hsc hst hct input tape
    word lower [] targetOrigin clockOrigin cells s.val s.property hs
    (by simpa using ht) (by simpa [cells, BitTape.shifted] using hc) present ended
  let a := Store.ofState r
  have ea : Executes input tape (.call (rawProgram source clock target))
      (11 * word.length + 4) s a := by
    convert Executes.call (rawProgram source clock target) s r (11 * word.length + 3) er
      (by simp [rawProgram, rpc]) using 1
  have ac : a.val.tapes clock = BitTape.shiftedEnd clockWord clockOrigin := by
    simpa [a, Store.ofState, cells, BitTape.shiftedEnd, hwidth] using rc
  obtain ⟨ew, wc⟩ := WordTransfer.rewind_shifted clock clockOrigin input tape clockWord a.val
    a.property ac
  let t := Store.ofState (Rewind.finishAt clock clockOrigin a.val)
  have et : Executes input tape (.call (Rewind.program clock))
      (4 * clockWord.length + 6) a t := by
    convert Executes.call (Rewind.program clock) a _ (4 * clockWord.length + 5) ew
      (by simp [Rewind.program, Rewind.finishAt]) using 1
  have finalClock : t.val.tapes clock = s.val.tapes clock := wc.trans hc.symm
  refine ⟨t, ?_, ?_, ?_, finalClock, rf.1, rf.2.2.1, ?_, ?_⟩
  · unfold code
    convert ea.seq et using 1
    rw [hwidth]
    omega
  · simpa [t, a, Store.ofState, Rewind.finishAt, hsc] using rs
  · simpa [t, a, Store.ofState, Rewind.finishAt, Ne.symm hct] using rt
  · refine ⟨rf.2.1, rf.2.2.2.1, rf.2.2.2.2.1, ?_, ?_, ?_⟩
    · intro j _ hj
      have js : j ≠ source := by simp_all
      have jt : j ≠ target := by simp_all
      by_cases jc : j = clock
      · subst j; exact finalClock
      · simpa [t, a, Store.ofState, Rewind.finishAt, jc] using rf.2.2.2.2.2.1 j js jc jt
    · simpa [t, a, Store.ofState, Rewind.finishAt] using
        rf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)
    · intro j hj
      simpa [t, a, Store.ofState, Rewind.finishAt, show j ≠ 24 by omega, show j ≠ 25 by omega] using
        rf.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)
  · intro j js jt
    by_cases jc : j = clock
    · subst j; exact finalClock
    · simpa [t,a,Store.ofState,Rewind.finishAt,jc] using rf.2.2.2.2.2.1 j js jc jt

theorem run (source clock target : ℕ) (hsc : source ≠ clock)
    (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word lower clockWord : List Bool)
    (targetOrigin clockOrigin : ℤ) (s : Store)
    (hwidth : clockWord.length = word.length)
    (hs : s.val.tapes source = BitTape.atEnd (lower ++ word))
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin})
    (hc : s.val.tapes clock = BitTape.shifted clockWord clockOrigin) :
    ∃ t : Store,
      (runPriced ((program source clock target).next input tape)
        (15 * word.length + 11) s.val).finished = some (t.place (code source clock target).size) ∧
      (runPriced ((program source clock target).next input tape)
        (15 * word.length + 11) s.val).instructions = 15 * word.length + 10 ∧
      t.val.tapes source = BitTape.atEnd lower ∧
      t.val.tapes target = BitTape.shifted word (targetOrigin - word.length) ∧
      t.val.tapes clock = s.val.tapes clock ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      Frame {source, target} s.val t.val := by
  obtain ⟨t, he, hs, ht, hc, ha, hm, hf, _⟩ := executes source clock target hsc hst hct
    input tape word lower clockWord targetOrigin clockOrigin s hwidth hs ht hc
  obtain ⟨finished, cost⟩ := he.compiled_run (15 * word.length + 11) (by omega)
  exact ⟨t, finished, cost, hs, ht, hc, ha, hm, hf⟩

end Maxwell.Cost.SourceCircuit.WordStack
