import Maxwell.Cost.BankArray.Prepare
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

/-- Shared arithmetic/address workspace; tape 7 is the read result. -/
def Scratch (s : BitRAMState) : Prop :=
  Blank s 0 ∧ Blank s 1 ∧ Blank s 2 ∧ Blank s 3 ∧
  Blank s 5 ∧ Blank s 6 ∧ Blank s 8 ∧ Blank s 9

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi, hr, ho, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hh => (kt i hh).trans (ht i hh),
    fun i h15 h24 h25 h26 h27 h28 h29 =>
      (kg i h15 h24 h25 h26 h27 h28 h29).trans (hg i h15 h24 h25 h26 h27 h28 h29)⟩

def costCap (width index base payload : List Bool) : ℕ :=
  ArrayAccess.costCap width index base (addressValue width) +
    40 * (width.length + index.length + base.length + payload.length + addressValue width + 3)

/-- A saved binary word with its head at the first cell. High zero bits are
allowed, as required by fixed-width arrays. -/
def Word (s : BitRAMState) (bank : ℕ) (bits : List Bool) : Prop :=
  ∃ origin, s.tapes bank = BitTape.shifted bits origin

def FrameExcept (bank : ℕ) (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → i ≠ bank → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem word_of_eq {s t : BitRAMState} {bank : ℕ} {bits : List Bool}
    (h : t.tapes bank = s.tapes bank) (hw : Word s bank bits) : Word t bank bits := by
  obtain ⟨origin, ho⟩ := hw
  exact ⟨origin, h.trans ho⟩

end Maxwell.Cost.BankArray
