import Maxwell.Cost.BankArray.Common

/-! Transfer the ordinary array scratch invariant across preserved tapes. -/
namespace Maxwell.Cost.BankArray

theorem Scratch.transfer {s t : BitRAMState} (h : Scratch s)
    (keep : ∀k∈({0,1,2,3,5,6,8,9}:Finset ℕ),t.tapes k=s.tapes k) : Scratch t := by
  rcases h with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
    RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
    RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
    RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩

#print axioms Scratch.transfer
end Maxwell.Cost.BankArray
