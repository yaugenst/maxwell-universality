import Maxwell.Cost.PositiveGraph.Initialize.Config
import Maxwell.Cost.PositiveGraph.Initialize.Eight

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Word Blank)

theorem Config.change_value {W d K value other : ℕ} {clock : List Bool} {s t : BitRAMState}
    (h : Config W d K value clock s) (hf : Frame s t)
    (hk : ∀ i, i ≠ 162 → t.tapes i=s.tapes i) (hv : Word t 162 other) :
    Config W d K other clock t := by
  obtain ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩ := h.scratch
  refine ⟨hf.numeric W d K h.numeric,BankArray.word_of_eq (hk 146 (by omega)) h.clockWord,
    ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,hv⟩
  · exact RationalAccumulator.blank_of_eq (hk 0 (by omega)) h0
  · exact RationalAccumulator.blank_of_eq (hk 1 (by omega)) h1
  · exact RationalAccumulator.blank_of_eq (hk 2 (by omega)) h2
  · exact RationalAccumulator.blank_of_eq (hk 3 (by omega)) h3
  · exact RationalAccumulator.blank_of_eq (hk 5 (by omega)) h5
  · exact RationalAccumulator.blank_of_eq (hk 6 (by omega)) h6
  · exact RationalAccumulator.blank_of_eq (hk 8 (by omega)) h8
  · exact RationalAccumulator.blank_of_eq (hk 9 (by omega)) h9
  · exact RationalAccumulator.blank_of_eq (hk 7 (by omega)) h.seven
  · exact RationalAccumulator.blank_of_eq (hk 37 (by omega)) h.temporary
  · exact RationalAccumulator.blank_of_eq (hk 160 (by omega)) h.cursor
  · exact RationalAccumulator.blank_of_eq (hk 161 (by omega)) h.count

theorem Config.eight {W d K : ℕ} {clock : List Bool}
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (h : Config W d K 0 clock s.val) :
    ∃ t, Executes input tape eightCode 46 s t ∧ Config W d K 8 clock t.val ∧
      t.val.memory=s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨t,he,hw,hm,hk,hf⟩ := eight_executes input tape s
    ((RationalAccumulator.zero_word_iff_blank s.val 162).mp h.valueWord)
  exact ⟨t,he,h.change_value hf hk hw,hm,hf⟩

theorem Config.clear {W d K : ℕ} {clock : List Bool}
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (h : Config W d K 8 clock s.val) :
    ∃ t, Executes input tape (.call (TapeOps.clear 162)) 28 s t ∧ Config W d K 0 clock t.val ∧
      t.val.memory=s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨origin,ho⟩ := h.valueWord
  obtain ⟨t,he,ht,hf⟩ := WordCall.clear 162 input tape (8:ℕ).bits origin s ho
  have hk (i : ℕ) (hi : i ≠ 162) : t.val.tapes i=s.val.tapes i := by simp [ht,hi]
  have ff : Frame s.val t.val := ⟨hf.2.1,hf.2.2.2.1,hf.2.2.2.2.1,
    fun i _ _ _ _ hi => hk i hi,fun i _ _ _ h26 h27 _ _ => hf.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨t,he,h.change_value ff hk ?_,hf.2.2.1,ff⟩
  exact ⟨origin+4,by simp [ht]; rfl⟩

end Maxwell.Cost.PositiveGraph.Initialize
