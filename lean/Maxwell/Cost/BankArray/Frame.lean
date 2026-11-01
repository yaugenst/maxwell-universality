import Maxwell.Cost.BankArray.Common

/-! Shared array scratch survives any operation preserving its low tapes. -/
namespace Maxwell.Cost.BankArray
open RationalAccumulator

theorem Scratch.of_tapes {s t : BitRAMState} (h : Scratch s)
    (keep : ∀i,i<10→t.tapes i=s.tapes i) : Scratch t :=
  ⟨blank_of_eq (keep 0 (by decide)) h.1,blank_of_eq (keep 1 (by decide)) h.2.1,
    blank_of_eq (keep 2 (by decide)) h.2.2.1,blank_of_eq (keep 3 (by decide)) h.2.2.2.1,
    blank_of_eq (keep 5 (by decide)) h.2.2.2.2.1,blank_of_eq (keep 6 (by decide)) h.2.2.2.2.2.1,
    blank_of_eq (keep 8 (by decide)) h.2.2.2.2.2.2.1,blank_of_eq (keep 9 (by decide)) h.2.2.2.2.2.2.2⟩

end Maxwell.Cost.BankArray
