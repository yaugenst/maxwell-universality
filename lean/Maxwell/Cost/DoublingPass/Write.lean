import Maxwell.Cost.DoublingPass.Read
import Maxwell.Cost.BankArray.Write

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)
open Maxwell.Logical.Routing

def writeCode : Code := .seq (BankArray.writeCode 80 81 85 89) (BankArray.writeCode 80 81 86 92)

/-- Store the two outputs using separately charged writes to the new arrays. -/
theorem write_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hi : addressValue index = j.val)
    (hsep : layout.Separated n) (s : Store) (cfg : Config layout index clock s.val)
    (scratch : BankArray.Scratch s.val)
    (h89 : Word s.val 89 (labelWord layout (saved.jump.get (saved.jump.get j))))
    (h92 : Word s.val 92 (labelWord layout (min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j)))))
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 60000 * (budget layout index + 1)^2 ∧
      Executes input tape writeCode cost s t ∧ BankArray.Scratch t.val ∧
      t.val.tapes 7 = s.val.tapes 7 ∧ t.val.memory = slotMemory layout saved j s.val.memory ∧
      (∀ k, k = 4 ∨ 10 ≤ k → t.val.tapes k = s.val.tapes k) ∧
      Config layout index clock t.val ∧ Frame s.val t.val := by
  let jumpWord := labelWord layout (saved.jump.get (saved.jump.get j))
  let minWord := labelWord layout (min (saved.minimum.get j) (saved.minimum.get (saved.jump.get j)))
  obtain ⟨ca, a, hca, ea, am, _, ass, a7, af⟩ :=
    BankArray.write_bank 80 81 85 89 (by omega) (by omega) (by omega) (by omega)
      input tape layout.width.bits index layout.newJump.bits jumpWord (words layout.width output.jump) j
      (RationalAccumulator.bits_nonempty hw) hi (by simp [jumpWord]) s scratch
      cfg.width cfg.index cfg.newJump h89 (by simpa using rep.newJump)
  have cfgA := cfg.of_frame (Frame.of_bank af)
  have a92 : Word a.val 92 minWord := BankArray.word_of_eq (af.2.2.2.1 92 (by omega)) h92
  have repM : BitArray.Represents a.val.memory layout.newMinimum layout.width (words layout.width output.minimum) := by
    rw [am]
    simpa only [addressValue_bits] using IncidenceEncoding.represents_write_disjoint rep.newMinimum
      layout.newJump layout.width j jumpWord (by simp [jumpWord]) hsep.outputs.symm
  obtain ⟨cb, t, hcb, et, tm, _, tss, t7, tf⟩ :=
    BankArray.write_bank 80 81 86 92 (by omega) (by omega) (by omega) (by omega)
      input tape layout.width.bits index layout.newMinimum.bits minWord (words layout.width output.minimum) j
      (RationalAccumulator.bits_nonempty hw) hi (by simp [minWord]) a ass
      cfgA.width cfgA.index cfgA.newMinimum a92 (by simpa using repM)
  have ff := (Frame.of_bank af).trans (Frame.of_bank tf)
  refine ⟨ca + cb, t, ?_, ea.seq et, tss, t7.trans a7, ?_,
    fun k hk => (tf.2.2.2.1 k hk).trans (af.2.2.2.1 k hk), cfg.of_frame ff, ff⟩
  · have hbound (base : ℕ) (payload : List Bool) (hb : base.bits.length ≤ budget layout index)
        (hp : payload.length = layout.width) :
        BankArray.costCap layout.width.bits index base.bits payload ≤ 30000 * (budget layout index + 1)^2 :=
      IncidencePass.array_cost_le _ _ _ _ _ (by dsimp [budget]; omega) (by dsimp [budget]; omega)
        hb (by dsimp [budget]; omega) (by simp only [addressValue_bits]; dsimp [budget]; omega)
    have haBound := hbound layout.newJump jumpWord (by dsimp [budget]; omega) (by simp [jumpWord])
    have hbBound := hbound layout.newMinimum minWord (by dsimp [budget]; omega) (by simp [minWord])
    omega
  · rw [tm, am]
    simp only [addressValue_bits, slotMemory, jumpWord, minWord]

end Maxwell.Cost.DoublingPass
