import Maxwell.Cost.NormalizedRecordParser.Natural
import Maxwell.Cost.DecoderParser.Primitives

namespace Maxwell.Cost.NormalizedRecordParser
open Structured

abbrev cursor (stream : List Bool) (position : ℤ) : BitTape :=
  {BitTape.ofList stream with head := position}

abbrev Frame := DecoderParser.Frame

def readNatural (target : ℕ) : Code :=
  .seq (.call (Natural.programOn target)) (.call DecoderParser.resetCounter)

theorem readNatural_executes (target : ℕ) (h10t : target ≠ 10) (h85t : target ≠ 85)
    (input : List Bool) (randomTape : ℕ → Bool)
    (n : ℕ) (preceding suffix : List Bool) (s : Store)
    (hsource : s.val.tapes 85 = cursor (preceding ++ (Codec.nat n ++ suffix)) preceding.length)
    (h10 : s.val.tapes 10 = BitTape.blank) (hout : s.val.tapes target = BitTape.blank) :
    ∃ cost t, Executes input randomTape (readNatural target) cost s t ∧
      cost ≤ 34 * n.bits.length + 17 ∧
      t.val.tapes 85 = cursor (preceding ++ (Codec.nat n ++ suffix))
        (preceding.length + (Codec.nat n).length) ∧
      t.val.tapes 10 = BitTape.blank ∧ t.val.tapes target = BitTape.atEnd n.bits ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.registers 23 = s.val.registers 23 ∧
      Frame {target,85} s.val t.val := by
  obtain ⟨cost, a, ea, haCost, hap, ha85, ha10, haTarget, haf⟩ :=
    Natural.steps_on target h10t h85t input randomTape n preceding suffix s.val s.property hsource h10 hout
  have e1 := Executes.call (Natural.programOn target) s a cost ea (by
    simp [Natural.programOn, BitRAM.renameTapes, Natural.program, hap, BitRAMInstruction.renameTapes])
  have e2 := DecoderParser.resetCounter_steps input randomTape (Store.ofState a) ha10
  let t := Store.ofState (DecoderParser.resetCounterState (Store.ofState a).val)
  have ht10 : t.val.tapes 10 = BitTape.blank := by
    simp [t, Store.ofState, DecoderParser.resetCounterState]
  have hsrc : a.tapes 85 = cursor (preceding ++ (Codec.nat n ++ suffix))
      (preceding.length + (Codec.nat n).length) := by
    apply BitTape.ext ha85
    simpa [hsource] using haf.2.2.2.2.2.1
  refine ⟨cost+3, t, ?_, by omega, ?_, ht10, ?_, haf.2.1,
    haf.2.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide), ?_⟩
  · exact e1.seq e2
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hsrc
  · simpa [t, Store.ofState, DecoderParser.resetCounterState, h10t] using haTarget
  · refine ⟨haf.1, haf.2.2.1, haf.2.2.2.1, haf.2.2.2.2.1, ?_⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    by_cases hi10 : i = 10
    · subst i; exact ht10.trans h10.symm
    simpa [t, Store.ofState, DecoderParser.resetCounterState, hi10] using
      haf.2.2.2.2.2.2.1 i hi10 hi.1 hi.2

def signProgram : BitRAM := ⟨[.readTape 85 23 28, .tapeRight 85, .halt]⟩

def signFinish (negative : Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 2
    registers := Function.update (Function.update s.registers 23 negative) 28 true
    tapes := Function.update s.tapes 85 {s.tapes 85 with head := (s.tapes 85).head + 1}}

theorem sign_executes (input : List Bool) (randomTape : ℕ → Bool)
    (negative : Bool) (s : Store) (hbit : (s.val.tapes 85).read = some negative) :
    Executes input randomTape (.call signProgram) 4 s (Store.ofState (signFinish negative s.val)) := by
  apply Executes.call signProgram s (signFinish negative s.val) 3
  · apply executeInstructions_sound (instructions := 2)
    simp [executeInstructions, BitRAM.next, signProgram, signFinish, hbit, s.property,
      BitRAMState.setRegister, BitRAMState.setTape]
  · rfl

theorem sign_frame (negative : Bool) (s : BitRAMState) : Frame {85} s (signFinish negative s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  simp only [Finset.mem_singleton] at hi
  simp [signFinish, hi]

end Maxwell.Cost.NormalizedRecordParser
