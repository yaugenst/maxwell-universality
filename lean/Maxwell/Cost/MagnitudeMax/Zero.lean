import Maxwell.Cost.MagnitudeMax.Save

namespace Maxwell.Cost.MagnitudeMax.Zero

open Structured RationalAccumulator

/-- A canonical zero word is empty. Reading presence therefore decides
whether the stored RHS maximum numerator is zero without changing it. -/
def code : Code := .seq (Code.atom (.readTape 86 88 89)) (Code.atom (.bitNot 90 89))

def finish (s : Store) : Store :=
  let u := Store.ofState (readTapeState s.val 86 88 89)
  Store.ofState (u.val.setRegister 90 (!u.val.registers 89))

theorem executes (n : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hword : Word s.val 86 n) :
    Executes input tape code 5 s (finish s) ∧
      (finish s).val.registers 90 = decide (n = 0) ∧
      (finish s).val.inputHead = s.val.inputHead ∧ DecoderParser.Frame ∅ s.val (finish s).val := by
  have hr : Executes input tape (Code.atom (.readTape 86 88 89)) 3 s
      (Store.ofState (readTapeState s.val 86 88 89)) := by
    apply Executes.atom (extra := 1)
    · simp [BitRAM.next, s.property, readTapeState]
    · simp [readTapeState, s.property]
  have hn := Executes.bitNot input tape (Store.ofState (readTapeState s.val 86 88 89)) 90 89
  refine ⟨hr.seq hn, ?_, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨origin, ho⟩ := hword
  have htest : n.bits.head?.isNone = decide (n = 0) := by
    by_cases hn : n = 0
    · simp [hn]
    · cases hb : n.bits with
      | nil =>
        have hv := address_bits n
        simp [hb, addressValue] at hv
        exact False.elim (hn hv.symm)
      | cons b bs => simp [hn]
  simpa [finish, Store.ofState, readTapeState, BitRAMState.setRegister, ho] using htest

end Maxwell.Cost.MagnitudeMax.Zero
