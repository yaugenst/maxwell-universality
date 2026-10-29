import Maxwell.Cost.ColorPass.Encoding

namespace Maxwell.Cost.ColorPass
open Structured DoublingPass
open BankArray (Word)

def writeCode : Code := BankArray.writeCode 86 81 85 91

/-- One actual write to the one-bit color array, using the constant width bank. -/
theorem write_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : State n) (output : Vector Bool n) (j : Fin n) (index clock : List Bool)
    (hone : layout.newMinimum = 1) (hi : addressValue index = j.val)
    (s : Store) (cfg : Config layout index clock s.val) (hs : BankArray.Scratch s.val)
    (h91 : Word s.val 91 [bit saved j]) (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 30000 * (budget layout index + 1)^2 ∧
      Executes input tape writeCode cost s t ∧ BankArray.Scratch t.val ∧
      t.val.tapes 7 = s.val.tapes 7 ∧ t.val.memory = slotMemory layout saved j s.val.memory ∧
      (∀ i, i = 4 ∨ 10 ≤ i → t.val.tapes i = s.val.tapes i) ∧
      Config layout index clock t.val ∧ DoublingPass.Frame s.val t.val := by
  obtain ⟨cost,t,hcost,et,tm,_,ts,t7,tf⟩ := BankArray.write_bank 86 81 85 91
    (by omega) (by omega) (by omega) (by omega) input tape (1 : ℕ).bits index layout.newJump.bits
    [bit saved j] (colorWords output) j (by decide) hi (by rw [addressValue_bits]; rfl) s hs
    (by simpa [hone] using cfg.newMinimum) cfg.index cfg.newJump h91 (by simpa only [addressValue_bits] using rep.output)
  refine ⟨cost,t,?_,et,ts,t7,?_,tf.2.2.2.1,cfg.of_frame (DoublingPass.Frame.of_bank tf),
    DoublingPass.Frame.of_bank tf⟩
  · apply hcost.trans
    exact IncidencePass.array_cost_le _ _ _ _ _ (by change 1 ≤ budget layout index; dsimp [budget]; omega)
      (by dsimp [budget]; omega) (by dsimp [budget]; omega)
      (by change 1 ≤ budget layout index; dsimp [budget]; omega) (by rw [addressValue_bits]; dsimp [budget]; omega)
  · simpa only [slotMemory, addressValue_bits,
      Nat.mul_one] using tm

end Maxwell.Cost.ColorPass
