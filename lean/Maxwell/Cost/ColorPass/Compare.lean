import Maxwell.Cost.ColorPass.Read
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.ColorPass
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

private theorem write_blank (origin : ℤ) (b : Bool) :
    ({BitTape.blank with head := origin} : BitTape).write (some b) = BitTape.shifted [b] origin := by
  apply BitTape.ext
  · rfl
  · funext k
    by_cases hk : k = origin
    · subst k; simp [BitTape.write, BitTape.blank, BitTape.shifted]
    · by_cases hle : origin ≤ k
      · have hgt : origin < k := by omega
        simp [BitTape.write, BitTape.blank, BitTape.shifted, hk, hle, hgt]
      · simp [BitTape.write, BitTape.blank, BitTape.shifted, hk, hle]

def compareCode : Code := .seq (BankArray.compareCode 89 90) (.atom (.writeTape 91 2))

/-- The output bit is written directly from the comparison register. -/
theorem compare_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : State n) (j : Fin n) (hn : n ≤ 2^layout.width)
    (s : Store) (h89 : Word s.val 89 (labelWord layout (saved.minimum.get j)))
    (h90 : Word s.val 90 (labelWord layout (saved.minimum.get (saved.jump.get j))))
    (h91 : Blank s.val 91) (hs : BankArray.Scratch s.val) :
    ∃ t, Executes input tape compareCode (80*layout.width+76) s t ∧
      Word t.val 91 [bit saved j] ∧ BankArray.Scratch t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → i ≠ 91 → t.val.tapes i = s.val.tapes i) ∧ DoublingPass.Frame s.val t.val := by
  obtain ⟨c, ec, cb, cs, cm, ck, cf⟩ := BankArray.compare_bank 89 90 (by omega) (by omega)
    input tape _ _ (by simp) s h89 h90 hs
  have cv : c.val.registers 2 = bit saved j := by
    apply Bool.eq_iff_iff.mpr
    simpa only [bit, decide_eq_true_eq, labelWord,
      IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (saved.minimum.get j).isLt hn),
      IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (saved.minimum.get (saved.jump.get j)).isLt hn),
      Fin.lt_def] using cb
  let t := Store.ofState (c.val.setTape 91 ((c.val.tapes 91).write (some (c.val.registers 2))))
  have et := Executes.writeTape input tape c 91 2
  have tk (i : ℕ) (hi : i ≠ 91) : t.val.tapes i = c.val.tapes i := by
    simp [t, Store.ofState, BitRAMState.setTape, hi]
  have tf : DoublingPass.Frame c.val t.val := by
    refine ⟨rfl,rfl,rfl,?_,fun _ _ _ _ _ _ _ _ => rfl⟩
    intro i _ hp
    exact tk i (by intro he; exact hp (he ▸ (by simp [Private])))
  obtain ⟨o, ho⟩ := h91
  refine ⟨t, ?_, ⟨o, ?_⟩, ?_, cm, fun i hi h91 => (tk i h91).trans (ck i hi),
    (DoublingPass.Frame.of_bank cf).trans tf⟩
  · convert ec.seq et using 1 <;> first | rfl | simp [labelWord]
  · simp only [t, Store.ofState, BitRAMState.setTape, Function.update_self, ck 91 (by omega), ho, cv]
    exact write_blank o (bit saved j)
  · rcases cs with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (tk 0 (by omega)) h0,
      RationalAccumulator.blank_of_eq (tk 1 (by omega)) h1,
      RationalAccumulator.blank_of_eq (tk 2 (by omega)) h2,
      RationalAccumulator.blank_of_eq (tk 3 (by omega)) h3,
      RationalAccumulator.blank_of_eq (tk 5 (by omega)) h5,
      RationalAccumulator.blank_of_eq (tk 6 (by omega)) h6,
      RationalAccumulator.blank_of_eq (tk 8 (by omega)) h8,
      RationalAccumulator.blank_of_eq (tk 9 (by omega)) h9⟩

end Maxwell.Cost.ColorPass
