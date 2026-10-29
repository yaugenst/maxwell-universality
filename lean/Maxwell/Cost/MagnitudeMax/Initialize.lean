import Maxwell.Cost.MagnitudeMax.Body

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

/-- Write the denominator of the initial raw pair 0/1 using two literal
Boolean instructions. The numerator is already the empty binary zero word. -/
def initializeCode : Code :=
  .seq (Code.atom (.literal 61 true)) (Code.atom (.writeTape 31 61))

def initialized (s : Store) : Store := Store.ofState
  {s.val with
    registers := Function.update s.val.registers 61 true
    tapes := Function.update s.val.tapes 31 (BitTape.ofList [true])}

private theorem blank_write_one : BitTape.blank.write (some true) = BitTape.ofList [true] := by
  apply BitTape.ext
  · rfl
  · funext i
    by_cases hi : i = 0
    · subst i; simp [BitTape.write, BitTape.blank, BitTape.ofList]
    · simp [BitTape.write, BitTape.blank, BitTape.ofList, hi]
      omega

theorem initialize_executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hblank : s.val.tapes 31 = BitTape.blank) :
    Executes input tape initializeCode 4 s (initialized s) := by
  have h1 := Executes.literal input tape s 61 true
  have h2 := Executes.writeTape input tape (Store.ofState (s.val.setRegister 61 true)) 31 61
  change Executes input tape ((Code.atom (.literal 61 true)).seq (Code.atom (.writeTape 31 61))) 4 s _
  convert h1.seq h2 using 1
  apply Subtype.ext
  simp [initialized, Store.ofState, BitRAMState.setRegister, BitRAMState.setTape,
    hblank, blank_write_one]

theorem initialized_other (s : Store) (i : ℕ) (hi : i ≠ 31) :
    (initialized s).val.tapes i = s.val.tapes i := by
  simp [initialized, Store.ofState, hi]

theorem initialized_bank (s : Store) (hbank : Bank s.val (bankOf (0, 0))) :
    Bank (initialized s).val (bankOf (0, 1)) := by
  intro i hi hi'
  by_cases he : i = 31
  · subst i
    refine ⟨0, ?_⟩
    simp [initialized, Store.ofState, bankOf]
  · have h := word_of_eq (initialized_other s i he) (hbank i hi hi')
    simpa [bankOf, he] using h

end Maxwell.Cost.MagnitudeMax
