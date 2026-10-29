import Maxwell.Cost.SignedRound.Frame

namespace Maxwell.Cost.SignedRound.Decision

open Structured

def program : BitRAM := ⟨[.readTape 2 26 27, .bitNot 36 23, .branch 35 3 4,
  .bitAnd 36 36 27, .halt]⟩

def finish (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 4
    registers := Function.update (Function.update (Function.update s.registers
      26 ((s.tapes 2).read.getD false)) 27 ((s.tapes 2).read.isSome))
      36 (if s.registers 35 then !s.registers 23 && (s.tapes 2).read.isSome else !s.registers 23)}

theorem steps (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (hp : s.pc = 0) :
    PricedSteps (program.next input tape) (if s.registers 35 then 5 else 4) s (finish s) := by
  cases hs : s.registers 35
  · apply executeInstructions_sound (instructions := 3)
    simp [executeInstructions, BitRAM.next, program, hp, hs, finish, BitRAMState.setRegister]
  · apply executeInstructions_sound (instructions := 4)
    simp [executeInstructions, BitRAM.next, program, hp, hs, finish, BitRAMState.setRegister]

theorem finish_frame (s : BitRAMState) : Frame 0 s (finish s) := by
  simp [Frame, finish]
  intro i _ hi h36
  simp [show i ≠ 26 by omega, show i ≠ 27 by omega, h36]

theorem canonical_nonempty (n : ℕ) : n.bits.head?.isSome = decide (0 < n) := by
  have hn : n.bits ≠ [] ↔ 0 < n := by
    constructor
    · intro h
      by_contra hn
      have he : n = 0 := Nat.eq_zero_of_not_pos hn
      exact h (by simp [he])
    · intro h he
      have hv := RationalAccumulator.address_bits n
      simp [he, addressValue] at hv
      omega
  apply Bool.eq_iff_iff.mpr
  simpa using hn

theorem executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (n : ℕ) (origin : ℤ) (negative borrow : Bool)
    (hw : s.val.tapes 2 = BitTape.shifted n.bits origin)
    (hs : s.val.registers 35 = negative) (hb : s.val.registers 23 = borrow) :
    ∃ cost, ∃ t : Store, cost ≤ 6 ∧ Executes input tape (.call program) cost s t ∧
      t.val.registers 36 = (if negative then !borrow && decide (0 < n) else !borrow) ∧
      Frame 0 s.val t.val := by
  refine ⟨(if s.val.registers 35 then 5 else 4) + 1, Store.ofState (finish s.val),
    by split <;> omega,
    Executes.call _ _ _ _ (steps input tape s.val s.property) (by simp [program, finish]), ?_,
    finish_frame s.val⟩
  simp [Store.ofState, finish, hw, hs, hb, canonical_nonempty]

end Maxwell.Cost.SignedRound.Decision
