import Maxwell.Cost.CalibrationMatrix.IndexedTerm
import Maxwell.Cost.BankArray.Increment
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.CalibrationMatrix

open Structured

def LoopFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ≠ 102 → i ≠ 103 → i ≠ 106 →
    t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem LoopFrame.refl (s : BitRAMState) : LoopFrame s s := by simp [LoopFrame]

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) :
    LoopFrame s u := by
  rcases h with ⟨hm, hi, hr, ho, ht, hg⟩
  rcases k with ⟨km, ki, kr, ko, kt, kg⟩
  exact ⟨km.trans hm, ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hi hj hk hl hm => (kt i hi hj hk hl hm).trans (ht i hi hj hk hl hm),
    fun i hi h24 h25 h26 h27 h28 h29 =>
      (kg i hi h24 h25 h26 h27 h28 h29).trans (hg i hi h24 h25 h26 h27 h28 h29)⟩

theorem LoopFrame.of_step {s t : BitRAMState} (h : StepFrame s t) : LoopFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i hi hj _ _ _ => h.2.2.2.2.1 i hi hj, h.2.2.2.2.2⟩

theorem LoopFrame.of_increment {s t : BitRAMState} {bank : ℕ} (hb : bank = 102 ∨ bank = 103)
    (hm : t.memory = s.memory) (h : BankArray.FrameExcept bank s t) : LoopFrame s t :=
  ⟨hm, h.1, h.2.1, h.2.2.1,
    fun i hi _ h102 h103 _ => h.2.2.2.1 i hi (by omega), h.2.2.2.2⟩

theorem LoopFrame.of_counter {s t : Store} (h : CountedShifted.Frame 106 s t) :
    LoopFrame s.val t.val := by
  rcases h with ⟨_, hi, hm, hr, ho, ht, hg⟩
  exact ⟨hm, hi, hr, ho, fun i _ _ _ _ h106 => ht i h106,
    fun i hi h24 h25 _ _ _ h29 => hg i (by omega) h24 h25 h29⟩

theorem Stored.of_loop {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (hf : LoopFrame s t) : Stored d t := by
  have keep (i : ℕ) (hi : i = 100 ∨ i = 101 ∨ 110 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  exact ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    BankArray.word_of_eq (keep 110 (by omega)) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by omega)) h.matrixNegativeBase,
    BankArray.word_of_eq (keep 112 (by omega)) h.vectorPositiveBase,
    BankArray.word_of_eq (keep 113 (by omega)) h.vectorNegativeBase,
    by simpa only [hf.1] using h.matrixPositive,
    by simpa only [hf.1] using h.matrixNegative,
    by simpa only [hf.1] using h.vectorPositive,
    by simpa only [hf.1] using h.vectorNegative⟩

theorem Ready.of_tapes {s t : BitRAMState} {v : ℕ → ℕ} (h : Ready s v)
    (keep : ∀ i, i < 10 ∨ (30 ≤ i ∧ i ≤ 36) → t.tapes i = s.tapes i) : Ready t v := by
  refine ⟨fun i hi hi' => RationalAccumulator.word_of_eq (keep i (Or.inr ⟨hi, hi'⟩)) (h.1 i hi hi'),
    ?_, RationalAccumulator.blank_of_eq (keep 7 (by omega)) h.2.2⟩
  rcases h.2.1 with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩

def iterationCode : Code := .seq indexedTermCode
  (.seq (BankArray.incrementCode 102) (BankArray.incrementCode 103))

/-- An indexed term and both actual counter increments form one fixed loop
body. The separate remaining-count tape106 survives every body execution. -/
theorem iteration {m n : ℕ} (d : Data m n) (B : ℕ) (hsized : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi : List Bool)
    (hmiLen : mi.length ≤ B) (hviLen : vi.length ≤ B) (i : Fin m) (j : Fin n)
    (hmi : addressValue mi = i.val) (hvi : addressValue vi = j.val)
    (positive negative : ℕ) (hp : positive.bits.length ≤ B) (hn : negative.bits.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues positive negative))
    (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ cost, ∃ t : Store, cost ≤ 510000*(B+2)^2 ∧ Executes input tape iterationCode cost s t ∧
      Ready t.val (dotValues (positive+d.positiveTerm i j) (negative+d.negativeTerm i j)) ∧
      Indices t.val (Increment.bits mi) (Increment.bits vi) ∧
      t.val.tapes 106 = s.val.tapes 106 ∧ LoopFrame s.val t.val := by
  obtain ⟨tcost, a, htcost, ha, har, haf⟩ := indexed_term d B hsized input tape mi vi
    hmiLen hviLen i j hmi hvi positive negative hp hn s hready hdata hindices
  have hai := hindices.of_frame haf
  obtain ⟨mcost, b, hmcost, hb, hbi, _, hbm, _, hbkeep, hbf⟩ := BankArray.increment_bank
    102 (by omega) input tape mi a hai.1 har.2.1
  have hbr := har.of_tapes (fun i hi => hbkeep i (by omega))
  have hbvi := BankArray.word_of_eq (hbkeep 103 (by omega)) hai.2
  obtain ⟨vcost, t, hvcost, ht, hti, _, htm, _, htkeep, htf⟩ := BankArray.increment_bank
    103 (by omega) input tape vi b hbvi hbr.2.1
  refine ⟨tcost+(mcost+vcost), t, ?_, ha.seq (hb.seq ht),
    hbr.of_tapes (fun i hi => htkeep i (by omega)),
    ⟨BankArray.word_of_eq (htkeep 102 (by omega)) hbi, hti⟩, ?_,
    ((LoopFrame.of_step haf).trans (LoopFrame.of_increment (Or.inl rfl) hbm hbf)).trans
      (LoopFrame.of_increment (Or.inr rfl) htm htf)⟩
  · nlinarith
  · exact (htkeep 106 (by omega)).trans ((hbkeep 106 (by omega)).trans
      (haf.2.2.2.2.1 106 (Or.inr (by omega)) (Or.inr (by omega))))

end Maxwell.Cost.CalibrationMatrix
