import Maxwell.Cost.BankArray.ReadCanonical
import Maxwell.Cost.CalibrationMatrix.SignedAccumulate

namespace Maxwell.Cost.CalibrationMatrix

open Structured
open RationalAccumulator (Bank Blank)

def Ready (s : BitRAMState) (v : ℕ → ℕ) : Prop :=
  Bank s v ∧ BankArray.Scratch s ∧ Blank s 7

def StepFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem StepFrame.trans {s t u : BitRAMState} (h : StepFrame s t) (k : StepFrame t u) :
    StepFrame s u := by
  rcases h with ⟨hm, hi, hr, ho, ht, hg⟩
  rcases k with ⟨km, ki, kr, ko, kt, kg⟩
  exact ⟨km.trans hm, ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hi hj => (kt i hi hj).trans (ht i hi hj),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem stepFrame_of_arithmetic {s t : BitRAMState} (h : RationalAccumulator.Frame s t) :
    StepFrame s t := by
  rcases h with ⟨_, hi, hm, hr, ho, ht, hg⟩
  exact ⟨hm, hi, hr, ho, fun i hi hb => ht i (by omega) hb,
    fun i hi h24 h25 h26 h27 _ _ => hg i hi h24 h25 h26 h27⟩

theorem Ready.arithmetic {s : BitRAMState} {v : ℕ → ℕ} (h : Ready s v) :
    RationalAccumulator.Scratch s 0 :=
  ⟨h.2.1.1, (RationalAccumulator.zero_word_iff_blank s 1).mpr h.2.1.2.1,
    h.2.1.2.2.1, h.2.1.2.2.2.1⟩

theorem ready_of_arithmetic {s t : BitRAMState} {v w : ℕ → ℕ} (h : Ready s v)
    (hb : Bank t w) (hs : RationalAccumulator.Scratch t 0) (hf : RationalAccumulator.Frame s t) :
    Ready t w := by
  have keep (i : ℕ) (hi : i < 10) (hi' : 4 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.2.1 i hi' (Or.inl (by omega))
  exact ⟨hb, ⟨hs.1, (RationalAccumulator.zero_word_iff_blank t 1).mp hs.2.1,
    hs.2.2.1, hs.2.2.2,
    RationalAccumulator.blank_of_eq (keep 5 (by omega) (by omega)) h.2.1.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 6 (by omega) (by omega)) h.2.1.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 8 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.1,
    RationalAccumulator.blank_of_eq (keep 9 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.2⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by omega) (by omega)) h.2.2⟩

/-- Load an array operand through the actual indexed read and canonical
trim routines. Persistent layout words and both accumulators survive. -/
theorem read_operand {n : ℕ} (widthBank indexBank baseBank clockBank target : ℕ)
    (hw : 100 ≤ widthBank) (hi : 100 ≤ indexBank) (hb : 100 ≤ baseBank)
    (hc : 100 ≤ clockBank) (ht : 32 ≤ target) (ht' : target ≤ 35)
    (input : List Bool) (tape : ℕ → Bool) (width index base clock : List Bool)
    (words : Vector (List Bool) n) (i : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = i.val)
    (hclock : clock.length = addressValue width) (s : Store) (v : ℕ → ℕ)
    (hready : Ready s.val v) (hzero : v target = 0)
    (hwidthBank : BankArray.Word s.val widthBank width)
    (hindexBank : BankArray.Word s.val indexBank index)
    (hbaseBank : BankArray.Word s.val baseBank base)
    (hclockBank : BankArray.Word s.val clockBank clock)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ BankArray.costCap width index base clock + 32*addressValue width+35 ∧
      Executes input tape (BankArray.readCanonicalCode widthBank indexBank baseBank clockBank target) cost s t ∧
      Ready t.val (Function.update v target (addressValue (words.get i))) ∧ StepFrame s.val t.val := by
  have hblank := hready.1 target (by omega) (by omega)
  rw [hzero, RationalAccumulator.zero_word_iff_blank] at hblank
  obtain ⟨cost, t, hcost, he, hout, hs, h7, hm, _, hf⟩ := BankArray.read_canonical
    widthBank indexBank baseBank clockBank target (by omega) (by omega) (by omega) (by omega)
      (by omega) input tape width index base clock words i hwidth hindex hclock s hready.2.1 hready.2.2
      hblank hwidthBank hindexBank hbaseBank hclockBank harray
  refine ⟨cost, t, hcost, he, ⟨?_, hs, h7⟩, ?_⟩
  · intro j hj hj'
    by_cases heq : j = target
    · subst j; simpa only [Function.update_self] using hout
    · simp only [Function.update_of_ne heq]
      exact RationalAccumulator.word_of_eq (hf.2.2.2.1 j (Or.inr (by omega)) heq)
        (hready.1 j hj hj')
  · exact ⟨hm, hf.1, hf.2.1, hf.2.2.1,
      fun j hj hjb => hf.2.2.2.1 j hj (by omega), hf.2.2.2.2⟩

end Maxwell.Cost.CalibrationMatrix
