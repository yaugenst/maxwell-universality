import Maxwell.Cost.ModeRead.Signed
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.PhysicalDecoder.Sign
open Structured RationalAccumulator

def code : Code := .atom (.writeTape 358 358)

/-- The loader's computed Boolean is stored as one raw bit, including false.
This is the sign field consumed by the canonical coefficient emitter. -/
theorem executes (negative : Bool) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hsign : s.val.registers 358 = negative) (hblank : Blank s.val 358) :
    ∃ t, Executes input tape code 2 s t ∧ BankArray.Word t.val 358 [negative] ∧
      BinaryPrecision.Frame {358} s.val t.val ∧ t.val.registers = s.val.registers := by
  obtain ⟨origin, hblank⟩ := hblank
  let t := Store.ofState (s.val.setTape 358 ((s.val.tapes 358).write (some (s.val.registers 358))))
  have ht : ({BitTape.blank with head := origin} : BitTape).write (some negative) =
      BitTape.shifted [negative] origin := by
    apply BitTape.ext
    · rfl
    · have h := congrArg BitTape.cells (BitTape.shiftedEnd_append_write [] origin negative)
      simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using h
  refine ⟨t, Executes.writeTape input tape s 358 358, ⟨origin, ?_⟩, ?_, rfl⟩
  · simp only [t, Store.ofState, BitRAMState.setTape, Function.update_self, hblank, hsign]
    exact ht
  · refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro j hj
    have hn : j≠358 := by simpa only [Finset.mem_singleton] using hj
    exact Function.update_of_ne hn _ _

end Maxwell.Cost.PhysicalDecoder.Sign
