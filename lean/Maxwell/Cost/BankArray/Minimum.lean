import Maxwell.Cost.BankArray.Compare
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.BankArray
open Structured
open RationalAccumulator (Blank)

def chooseMinimum (xs ys : List Bool) : List Bool :=
  if addressValue xs < addressValue ys then xs else ys

theorem chooseMinimum_value (xs ys : List Bool) :
    addressValue (chooseMinimum xs ys) = min (addressValue xs) (addressValue ys) := by
  unfold chooseMinimum
  split_ifs with h
  · exact (min_eq_left (le_of_lt h)).symm
  · exact (min_eq_right (le_of_not_gt h)).symm

theorem chooseMinimum_length (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (chooseMinimum xs ys).length = xs.length := by
  unfold chooseMinimum
  split_ifs <;> omega

theorem chooseMinimum_word (width x y : ℕ) (hx : x < 2 ^ width) (hy : y < 2 ^ width) :
    chooseMinimum (IncidenceEncoding.word width x) (IncidenceEncoding.word width y) =
      IncidenceEncoding.word width (min x y) := by
  simp only [chooseMinimum, IncidenceEncoding.word_value width x hx, IncidenceEncoding.word_value width y hy]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]

def selectMinimumCode (left right target : ℕ) : Code :=
  .branch 2 (.call (WordTransfer.clone left target)) (.call (WordTransfer.clone right target))

theorem select_minimum (left right target : ℕ) (hlt : left ≠ target) (hrt : right ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (s : Store) (hxs : Word s.val left xs) (hys : Word s.val right ys)
    (origin : ℤ) (ht : s.val.tapes target = {BitTape.blank with head := origin})
    (hcompare : s.val.registers 2 = true ↔ addressValue xs < addressValue ys) :
    ∃ t, Executes input tape (selectMinimumCode left right target) (15 * xs.length + 18) s t ∧
      t.val.tapes = Function.update s.val.tapes target (BitTape.shifted (chooseMinimum xs ys) origin) ∧
      Control s.val t.val := by
  by_cases h : addressValue xs < addressValue ys
  · obtain ⟨sourceOrigin, hs⟩ := hxs
    obtain ⟨t, et, htapes, hf⟩ := WordCall.clone left target hlt input tape xs sourceOrigin origin s hs ht
    refine ⟨t, ?_, by simpa [chooseMinimum, h] using htapes, DecoderFetch.Control.of_transfer hf⟩
    convert Executes.yes (no := .call (WordTransfer.clone right target)) (hcompare.mpr h) et using 1 <;>
      first | rfl | omega
  · obtain ⟨sourceOrigin, hs⟩ := hys
    obtain ⟨t, et, htapes, hf⟩ := WordCall.clone right target hrt input tape ys sourceOrigin origin s hs ht
    have hfalse : s.val.registers 2 = false := by
      cases hv : s.val.registers 2 with
      | false => rfl
      | true => exact False.elim (h (hcompare.mp hv))
    refine ⟨t, ?_, by simpa [chooseMinimum, h] using htapes, DecoderFetch.Control.of_transfer hf⟩
    convert Executes.no (yes := .call (WordTransfer.clone left target)) hfalse et using 1 <;>
      first | rfl | omega

def minimumCode (left right target : ℕ) : Code :=
  .seq (compareCode left right) (selectMinimumCode left right target)

/-- A fixed finite program selects the unsigned minimum of two saved words.
The chosen word is copied exactly; the inputs and all scratch are retained. -/
theorem minimum_bank (left right target : ℕ) (hl : 10 ≤ left) (hr : 10 ≤ right)
    (ht : 10 ≤ target) (hlt : left ≠ target) (hrt : right ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (s : Store) (hxs : Word s.val left xs) (hys : Word s.val right ys)
    (hblank : Blank s.val target) (hs : Scratch s.val) :
    ∃ t, Executes input tape (minimumCode left right target) (95 * xs.length + 92) s t ∧
      Word t.val target (chooseMinimum xs ys) ∧ Scratch t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → i ≠ target → t.val.tapes i = s.val.tapes i) ∧ FrameExcept target s.val t.val := by
  obtain ⟨c, ec, hc2, hcs, hcm, hkeep, hcf⟩ := compare_bank left right hl hr input tape xs ys hlen s hxs hys hs
  obtain ⟨origin, hb⟩ := hblank
  obtain ⟨t, et, htapes, tf⟩ := select_minimum left right target hlt hrt input tape xs ys hlen c
    (word_of_eq (hkeep left (by omega)) hxs) (word_of_eq (hkeep right (by omega)) hys)
    origin ((hkeep target (by omega)).trans hb) hc2
  have keep (i : ℕ) (hi : 3 ≤ i) (hit : i ≠ target) : t.val.tapes i = s.val.tapes i := by
    rw [htapes]
    simpa [hit] using hkeep i hi
  refine ⟨t, ?_, ⟨origin, by simp [htapes]⟩, ?_, tf.2.2.2.1.trans hcm, keep, ?_⟩
  · convert ec.seq et using 1 <;> first | rfl | omega
  · have keepScratch (i : ℕ) (hi : i < 10) : t.val.tapes i = c.val.tapes i := by
      simp [htapes, show i ≠ target by omega]
    rcases hcs with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keepScratch 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (keepScratch 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (keepScratch 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (keepScratch 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (keepScratch 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (keepScratch 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (keepScratch 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (keepScratch 9 (by omega)) h9⟩
  · exact ⟨tf.1.trans hcf.1, tf.2.1.trans hcf.2.1, tf.2.2.1.trans hcf.2.2.1,
      fun i hi hit => keep i (by omega) hit,
      fun i hi h24 h25 h26 h27 h28 h29 =>
        (tf.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
          (hcf.2.2.2.2 i hi h24 h25 h26 h27 h28 h29)⟩

end Maxwell.Cost.BankArray
