import Maxwell.Cost.Multiplication.Program

namespace Maxwell.Cost

theorem addBits_length_ge (carry : Bool) (xs ys : List Bool) :
    max xs.length ys.length ≤ (addBits carry xs ys).length := by
  induction xs generalizing carry ys with
  | nil =>
    induction ys generalizing carry with
    | nil => simp
    | cons y ys ih =>
      simpa [addBits] using Nat.add_le_add_right (ih (xor (false && y) ((xor false y) && carry))) 1
  | cons x xs ih =>
    cases ys with
    | nil =>
      simpa [addBits] using Nat.add_le_add_right (ih (xor (x && false) ((xor x false) && carry)) []) 1
    | cons y ys =>
      simpa [addBits] using Nat.add_le_add_right (ih (xor (x && y) ((xor x y) && carry)) ys) 1

theorem Rewind.shiftedEnd_steps (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (ht : s.tapes workTape = BitTape.shiftedEnd bits origin) :
    PricedSteps ((program workTape).next input randomTape) (4 * bits.length + 5) s
      (finishAt workTape origin s) := by
  apply stepsAt workTape origin input randomTape bits.length s hpc
  · simp [ht, BitTape.shiftedEnd]
  · simp [ht, BitTape.shiftedEnd, BitTape.shifted]
  · intro k hk
    refine ⟨bits[k], ?_⟩
    simp [ht, BitTape.shiftedEnd, BitTape.shifted, hk]

theorem Rewind.finishAt_shiftedEnd (workTape : ℕ) (origin : ℤ) (bits : List Bool)
    (s : BitRAMState) (ht : s.tapes workTape = BitTape.shiftedEnd bits origin) :
    (finishAt workTape origin s).tapes workTape = BitTape.shifted bits origin := by
  simp [finishAt, ht, BitTape.shiftedEnd, BitTape.shifted]

theorem RewindOvershoot.shifted_steps (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (advance : ℕ)
    (hbits : 0 < bits.length) (hadvance : bits.length ≤ advance)
    (s : BitRAMState) (hpc : s.pc = 0)
    (ht : s.tapes workTape = {BitTape.shifted bits origin with head := origin + advance}) :
    PricedSteps ((program workTape).next input randomTape) (4 * advance + 6) s
      (finish workTape origin s) := by
  have hsum : bits.length + (advance - bits.length) = advance := by omega
  have hs := steps workTape origin input randomTape bits.length (advance - bits.length)
    hbits s hpc (by simp [ht]; omega)
    (by simp [ht, BitTape.shifted])
    (by intro k hk; exact ⟨bits[k], by simp [ht, BitTape.shifted, hk]⟩)
    (by intro k hk; simp [ht, BitTape.shifted, add_assoc]; omega)
  simpa [hsum] using hs

theorem RewindOvershoot.finish_shifted (workTape : ℕ) (origin : ℤ) (bits : List Bool)
    (advance : ℕ) (s : BitRAMState)
    (ht : s.tapes workTape = {BitTape.shifted bits origin with head := origin + advance}) :
    (finish workTape origin s).tapes workTape = BitTape.shifted bits origin := by
  simp [finish, Rewind.finishAt, ht, BitTape.shifted]

end Maxwell.Cost
