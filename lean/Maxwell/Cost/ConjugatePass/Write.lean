import Maxwell.Cost.ConjugatePass.Encoding

namespace Maxwell.Cost.ConjugatePass
open Structured DoublingPass
open BankArray (Word)

def writeCode : Code := BankArray.writeCode 80 81 86 90

/-- One actual fixed-width write of the composed lookup. -/
theorem write_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hi : addressValue index = j.val)
    (s : Store) (cfg : Config layout index clock s.val) (hs : BankArray.Scratch s.val)
    (h90 : Word s.val 90 (IncidenceEncoding.word layout.width (value saved j).val)) (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 30000 * (budget layout index + 1)^2 ∧
      Executes input tape writeCode cost s t ∧ BankArray.Scratch t.val ∧
      t.val.tapes 7 = s.val.tapes 7 ∧ t.val.memory = slotMemory layout saved j s.val.memory ∧
      (∀ i, i = 4 ∨ 10 ≤ i → t.val.tapes i = s.val.tapes i) ∧
      Config layout index clock t.val ∧ DoublingPass.Frame s.val t.val := by
  obtain ⟨cost,t,hcost,et,tm,_,ts,t7,tf⟩ := BankArray.write_bank 80 81 86 90
    (by omega) (by omega) (by omega) (by omega) input tape layout.width.bits index layout.newMinimum.bits
    (IncidenceEncoding.word layout.width (value saved j).val) output j
    (RationalAccumulator.bits_nonempty hw) hi (by simp only [IncidenceEncoding.word_length,addressValue_bits]) s hs
    cfg.width cfg.index cfg.newMinimum h90 (by simpa only [addressValue_bits] using rep.output)
  refine ⟨cost,t,?_,et,ts,t7,?_,tf.2.2.2.1,cfg.of_frame (DoublingPass.Frame.of_bank tf),
    DoublingPass.Frame.of_bank tf⟩
  · apply hcost.trans
    apply IncidencePass.array_cost_le
    · dsimp [budget]; omega
    · dsimp [budget]; omega
    · dsimp [budget]; omega
    · simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega
    · simp only [addressValue_bits]; dsimp [budget]; omega
  · simpa only [slotMemory,addressValue_bits] using tm

end Maxwell.Cost.ConjugatePass
