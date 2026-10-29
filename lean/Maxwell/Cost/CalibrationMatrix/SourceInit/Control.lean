import Maxwell.Cost.CalibrationMatrix.SourceInit.Data
import Maxwell.Cost.CalibrationMatrix.Assign

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured
open RationalAccumulator (Blank)

theorem word_nil_of_blank {s : BitRAMState} {i : ℕ} (h : Blank s i) : BankArray.Word s i [] := by
  obtain ⟨origin, ho⟩ := h
  exact ⟨origin, by simpa only [BitTape.shifted, BitTape.blank, List.length_nil,
    List.getElem?_nil, ite_self] using ho⟩

theorem load_count {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (source target : ℕ) (hsource : 100 ≤ source) (htarget : target = 106 ∨ target = 108)
    (hne : source ≠ target) (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (s : Store) (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hword : BankArray.Word s.val source count) (hblank : Blank s.val target) :
    ∃ t, Executes input tape (Assign.code source target) (15*count.length+21) s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d words t.val ∧ BankArray.Word t.val target count ∧
      MatrixFrame s.val t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨t, he, hw, ht, hf⟩ := Assign.executes source target hne input tape count [] s hword
    (word_nil_of_blank hblank)
  refine ⟨t, by simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_comm 4] using he,
    hready.of_tapes (fun i hi => ht i (by omega)),
    hdata.of_tapes_memory hf.2.2.1 (fun i hi => ht i (by omega)), hw, ?_, hf.2.2.1, ht⟩
  exact ⟨hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i _ _ _ _ _ _ h106 h108 => ht i (by omega),
    fun i _ h24 h25 h26 h27 _ _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

theorem clear_cursor {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (target : ℕ) (htarget : target = 102 ∨ target = 104)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (s : Store)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hword : BankArray.Word s.val target word) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6*word.length+4) s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d words t.val ∧ BankArray.Word t.val target [] ∧
      MatrixFrame s.val t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨origin, ho⟩ := hword
  obtain ⟨t, he, ht, hf⟩ := WordCall.clear target input tape word origin s ho
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i := by simp [ht, hi]
  refine ⟨t, he, hready.of_tapes (fun i hi => keep i (by omega)),
    hdata.of_tapes_memory hf.2.2.1 (fun i hi => keep i (by omega)),
    word_nil_of_blank ⟨origin+word.length, by simp [ht]⟩, ?_, hf.2.2.1, keep⟩
  exact ⟨hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i _ _ _ h102 _ h104 _ _ => keep i (by omega),
    fun i _ _ _ h26 h27 _ _ => hf.2.2.2.2.2.2 i h26 h27⟩

end Maxwell.Cost.CalibrationMatrix.SourceInit
