import Maxwell.Cost.SourceCircuit.HornerData

namespace Maxwell.Cost.SourceCircuit.HornerTerm
open HornerLoop

def initial (next gates : List Bool) (leaves : List (List Bool)) : Data where
  next := Increment.bits next
  accumulator := next
  gates := gates ++ zeroTag
  leaves := leaves

def signed (negative : Bool) (d : Data) : Data :=
  if negative then {
    next := Increment.bits d.next
    accumulator := d.next
    gates := d.gates ++ negativeTag ++ d.accumulator
    leaves := d.leaves }
  else d

theorem step_next (bit : Bool) (d : Data) :
    addressValue (step bit d).next = addressValue d.next + 1 + bit.toNat := by
  cases bit <;> simp [step,Increment.bits_value]

theorem fold_next (bits : List Bool) (d : Data) :
    addressValue (bits.foldr step d).next = addressValue d.next + bits.length + bits.count true := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    rw [List.foldr_cons,step_next,ih]
    cases b <;> simp <;> omega

theorem initial_valid (width : ℕ) (bits next gates : List Bool) (leaves : List (List Bool))
    (hlen : next.length = width) (hcount : leaves.length = bits.count true)
    (hleaves : ∀ word ∈ leaves, word.length = width)
    (hroom : addressValue next + 1 + bits.length + bits.count true < 2^width) :
    Valid width bits (initial next gates leaves) := by
  refine ⟨?_,hlen,hcount,hleaves,?_⟩
  · change (Increment.bits next).length = width
    rw [increment_length next (by rw [hlen]; omega),hlen]
  · simpa [initial,Increment.bits_value] using hroom

theorem signed_valid (width : ℕ) (negative : Bool) (d : Data)
    (h : Valid width [] d) (hroom : addressValue d.next + negative.toNat < 2^width) :
    Valid width [] (signed negative d) := by
  cases negative with
  | false => exact h
  | true =>
    refine ⟨?_,h.nextLength,h.leavesCount,h.leafLength,?_⟩
    · change (Increment.bits d.next).length = width
      rw [increment_length d.next (by rw [h.nextLength]; simpa using hroom),h.nextLength]
    · simpa [signed,Increment.bits_value] using hroom

end Maxwell.Cost.SourceCircuit.HornerTerm
