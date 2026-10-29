import Maxwell.Cost.DoublingPass.Common

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

/-- Read one saved Fin-valued array through the actual binary index bank. -/
theorem read_one {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (index clock lookup : List Bool) (values : Vector (Fin n) n)
    (base indexBank baseBank target : ℕ) (j : Fin n)
    (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (ht : Private target)
    (hw : 0 < layout.width) (hl : addressValue lookup = j.val)
    (hc : clock.length = layout.width)
    (hll : lookup.length ≤ budget layout index) (hbl : base.bits.length ≤ budget layout index)
    (s : Store) (cfg : Config layout index clock s.val) (scratch : BankArray.Scratch s.val)
    (empty7 : Blank s.val 7) (emptyTarget : Blank s.val target)
    (hlookup : Word s.val indexBank lookup) (hbase : Word s.val baseBank base.bits)
    (harray : BitArray.Represents s.val.memory base layout.width (words layout.width values)) :
    ∃ cost t, cost ≤ 35000 * (budget layout index + 1)^2 ∧
      Executes input tape (BankArray.readBankCode 80 indexBank baseBank 83 target) cost s t ∧
      Word t.val target (IncidenceEncoding.word layout.width (values.get j).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory = s.val.memory ∧
      Config layout index clock t.val ∧ BankArray.FrameExcept target s.val t.val := by
  obtain ⟨cost, t, hcost, he, hword, hscratch, h7, hm, _, hf⟩ :=
    BankArray.read_bank 80 indexBank baseBank 83 target (by omega) hi hb (by omega)
      (by dsimp [Private] at ht; omega) input tape layout.width.bits lookup base.bits clock
      (words layout.width values) j (RationalAccumulator.bits_nonempty hw) hl
      (by simpa using hc) s scratch empty7 emptyTarget cfg.width hlookup hbase cfg.clock
      (by simpa using harray)
  refine ⟨cost, t, ?_, he, by simpa using hword, hscratch, h7, hm,
    cfg.of_frame (Frame.of_except ht hf), hf⟩
  have hcap := IncidencePass.array_cost_le layout.width.bits lookup base.bits clock (budget layout index)
    (by dsimp [budget]; omega) hll hbl (by dsimp [budget]; omega)
    (by simp only [addressValue_bits]; dsimp [budget]; omega)
  have hwidth : layout.width ≤ budget layout index := by dsimp [budget]; omega
  simp only [addressValue_bits] at hcost
  nlinarith

end Maxwell.Cost.DoublingPass
