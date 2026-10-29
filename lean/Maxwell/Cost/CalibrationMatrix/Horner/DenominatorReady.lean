import Maxwell.Cost.CalibrationMatrix.Horner.Inverse
import Maxwell.Cost.CalibrationMatrix.Horner.Denominator

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank Word)

theorem Denominator.Frame.keep_work {s t : BitRAMState} (h : Denominator.Frame s t)
    (i : ℕ) (hi : 4 ≤ i) (hb : i < 30 ∨ 36 < i) (hi' : i ≤ 140) : t.tapes i = s.tapes i :=
  h.2.2.2.2.2.1 i hi hb (by omega) (by omega)

theorem WorkReady.after_denominator {s t : BitRAMState} {count : List Bool} {B : ℕ}
    (h : WorkReady count B s) (hb : RationalAccumulator.Bank t (fun _ => 0))
    (hs : RationalAccumulator.Scratch t 0) (hf : Denominator.Frame s t) : WorkReady count B t := by
  obtain ⟨vi,hvi,hvl,hr,hi,h104,h107,h106,h37,h108,h109⟩ := h
  have keep (i : ℕ) (hi : 4 ≤ i) (hj : i < 30 ∨ 36 < i) (hk : i ≤ 140) : t.tapes i = s.tapes i :=
    hf.keep_work i hi hj hk
  have hrt : CalibrationMatrix.Ready t (dotValues 0 0) :=
    ⟨by simpa [dotValues] using hb,
      ⟨hs.1,(RationalAccumulator.zero_word_iff_blank t 1).mp hs.2.1,hs.2.2.1,hs.2.2.2,
        RationalAccumulator.blank_of_eq (keep 5 (by omega) (Or.inl (by omega)) (by omega)) hr.2.1.2.2.2.2.1,
        RationalAccumulator.blank_of_eq (keep 6 (by omega) (Or.inl (by omega)) (by omega)) hr.2.1.2.2.2.2.2.1,
        RationalAccumulator.blank_of_eq (keep 8 (by omega) (Or.inl (by omega)) (by omega)) hr.2.1.2.2.2.2.2.2.1,
        RationalAccumulator.blank_of_eq (keep 9 (by omega) (Or.inl (by omega)) (by omega)) hr.2.1.2.2.2.2.2.2.2⟩,
      RationalAccumulator.blank_of_eq (keep 7 (by omega) (Or.inl (by omega)) (by omega)) hr.2.2⟩
  exact ⟨vi,hvi,hvl,hrt,
    ⟨BankArray.word_of_eq (keep 102 (by omega) (Or.inr (by omega)) (by omega)) hi.1,
      BankArray.word_of_eq (keep 103 (by omega) (Or.inr (by omega)) (by omega)) hi.2⟩,
    BankArray.word_of_eq (keep 104 (by omega) (Or.inr (by omega)) (by omega)) h104,
    BankArray.word_of_eq (keep 107 (by omega) (Or.inr (by omega)) (by omega)) h107,
    RationalAccumulator.blank_of_eq (keep 106 (by omega) (Or.inr (by omega)) (by omega)) h106,
    RationalAccumulator.blank_of_eq (keep 37 (by omega) (Or.inr (by omega)) (by omega)) h37,
    RationalAccumulator.blank_of_eq (keep 108 (by omega) (Or.inr (by omega)) (by omega)) h108,
    RationalAccumulator.blank_of_eq (keep 109 (by omega) (Or.inr (by omega)) (by omega)) h109⟩

theorem Denominator.Frame.scale_stored {n : ℕ} {s t : BitRAMState} {d : Scale.Data n}
    {words : Fin 4 → Vector (List Bool) n} (h : Denominator.Frame s t) (hs : Scale.Stored d words s) :
    Scale.Stored d words t := by
  have keep (i : ℕ) (hi : 100 ≤ i) (hi' : i ≤ 140) : t.tapes i = s.tapes i :=
    h.keep_work i (by omega) (Or.inr (by omega)) hi'
  refine ⟨BankArray.word_of_eq (keep 100 (by omega) (by omega)) hs.width,
    BankArray.word_of_eq (keep 101 (by omega) (by omega)) hs.clock,?_,
    RationalAccumulator.word_of_eq (keep 126 (by omega) (by omega)) hs.K,
    fun i => by simpa only [h.2.2.1] using hs.arrays i⟩
  intro i
  apply BankArray.word_of_eq (keep _ (by have := Scale.baseBank_ge i;omega) ?_) (hs.bases i)
  dsimp [Scale.baseBank]
  split_ifs <;> omega

theorem Denominator.Frame.ports {n : ℕ} {s t : BitRAMState} {d : Data n}
    {ip iq op oq : Fin 12} (h : Denominator.Frame s t) (hp : Ports d ip iq op oq s) : Ports d ip iq op oq t :=
  ⟨BankArray.word_of_eq (h.keep_work 112 (by omega) (Or.inr (by omega)) (by omega)) hp.inputPositive,
    BankArray.word_of_eq (h.keep_work 113 (by omega) (Or.inr (by omega)) (by omega)) hp.inputNegative,
    BankArray.word_of_eq (h.keep_work 114 (by omega) (Or.inr (by omega)) (by omega)) hp.outputPositive,
    BankArray.word_of_eq (h.keep_work 115 (by omega) (Or.inr (by omega)) (by omega)) hp.outputNegative⟩

/-- The charged denominator constructor composes directly after the inverse
numerator and leaves its actual output arrays and pairing controls intact. -/
theorem denominator_ready {n : ℕ} (l : Denominator.Layout) (D U V N B : ℕ)
    (hw : Denominator.Widths D U V N B) (d : Scale.Data n) (words : Fin 4 → Vector (List Bool) n)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool) (s : Store)
    (hready : WorkReady count B s.val) (hdata : Scale.Stored d words s.val)
    (hD : Word s.val l.denominator D) (hU : Word s.val l.numeratorScale U)
    (hV : Word s.val l.denominatorScale V) (hN : Word s.val l.count N)
    (h141 : Blank s.val 141) (h142 : Blank s.val 142) :
    ∃ cost, ∃ t : Store, cost ≤ Denominator.costCap N B ∧
      Executes input tape (Denominator.code l) cost s t ∧ WorkReady count B t.val ∧
      Scale.Stored d words t.val ∧ Word t.val 142 (Denominator.value D U V N) ∧
      Blank t.val 141 ∧ Denominator.Frame s.val t.val := by
  obtain ⟨vi,hvi,hvl,hr,ht⟩ := hready
  have hbank : RationalAccumulator.Bank s.val (fun _ => 0) := by simpa [dotValues] using hr.1
  obtain ⟨cost,t,hcost,he,hden,hb,hs,h141,hf⟩ := Denominator.executes l D U V N B hw input tape s
    hbank hr.arithmetic hD hU hV hN h141 h142
  exact ⟨cost,t,hcost,he,WorkReady.after_denominator ⟨vi,hvi,hvl,hr,ht⟩ hb hs hf,
    hf.scale_stored hdata,hden,h141,hf⟩

end Maxwell.Cost.CalibrationMatrix.Horner
