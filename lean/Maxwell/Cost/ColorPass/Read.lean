import Maxwell.Cost.ColorPass.Encoding
import Maxwell.Cost.DoublingPass.ReadOne

namespace Maxwell.Cost.ColorPass
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

abbrev labelWord (layout : Layout) {n : ℕ} (label : Fin n) : List Bool :=
  IncidenceEncoding.word layout.width label.val

def readCode : Code := .seq (BankArray.readBankCode 80 81 82 83 88)
  (.seq (BankArray.readBankCode 80 81 84 83 89) (BankArray.readBankCode 80 88 84 83 90))

/-- The indirect lookup uses the stored pairing value, never a host index. -/
theorem read_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : State n) (output : Vector Bool n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (s : Store) (cfg : Config layout index clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 105000 * (budget layout index + 1)^2 ∧
      Executes input tape readCode cost s t ∧
      Word t.val 88 (labelWord layout (saved.jump.get j)) ∧
      Word t.val 89 (labelWord layout (saved.minimum.get j)) ∧
      Word t.val 90 (labelWord layout (saved.minimum.get (saved.jump.get j))) ∧
      Blank t.val 91 ∧ Blank t.val 92 ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory = s.val.memory ∧ Config layout index clock t.val ∧ DoublingPass.Frame s.val t.val := by
  rcases work with ⟨scratch, empty7, emptyPrivate⟩
  obtain ⟨ca, a, hca, ea, a88, ass, a7, am, ac, af⟩ :=
    DoublingPass.read_one input tape layout index clock index saved.jump layout.oldJump 81 82 88 j
      (by omega) (by omega) (by simp [Private]) hw hi hc
      (by dsimp [budget]; omega) (by dsimp [budget]; omega) s cfg scratch empty7
      (emptyPrivate 88 (by simp [Private])) cfg.index cfg.oldJump rep.jump
  obtain ⟨cb, b, hcb, eb, b89, bss, b7, bm, bc, bf⟩ :=
    DoublingPass.read_one input tape layout index clock index saved.minimum layout.oldMinimum 81 84 89 j
      (by omega) (by omega) (by simp [Private]) hw hi hc
      (by dsimp [budget]; omega) (by dsimp [budget]; omega) a ac ass a7
      (RationalAccumulator.blank_of_eq (af.2.2.2.1 89 (by omega) (by omega))
        (emptyPrivate 89 (by simp [Private]))) ac.index ac.oldMinimum (by simpa [am] using rep.minimum)
  have bkeep (k : ℕ) (hk : 10 ≤ k) (h88 : k ≠ 88) (h89 : k ≠ 89) : b.val.tapes k = s.val.tapes k :=
    (bf.2.2.2.1 k (Or.inr hk) h89).trans (af.2.2.2.1 k (Or.inr hk) h88)
  have b88 := BankArray.word_of_eq (bf.2.2.2.1 88 (by omega) (by omega)) a88
  have indirectValue : addressValue (labelWord layout (saved.jump.get j)) = (saved.jump.get j).val :=
    IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (saved.jump.get j).isLt hn)
  obtain ⟨cc, t, hcc, et, t90, tss, t7, tm, tc, tf⟩ :=
    DoublingPass.read_one input tape layout index clock (labelWord layout (saved.jump.get j)) saved.minimum
      layout.oldMinimum 88 84 90 (saved.jump.get j) (by omega) (by omega) (by simp [Private])
      hw indirectValue hc (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega)
      (by dsimp [budget]; omega) b bc bss b7
      (RationalAccumulator.blank_of_eq (bkeep 90 (by omega) (by omega) (by omega))
        (emptyPrivate 90 (by simp [Private]))) b88 bc.oldMinimum
      (by simpa [bm, am] using rep.minimum)
  have keep (k : ℕ) (hk : 10 ≤ k) (h88 : k ≠ 88) (h89 : k ≠ 89) (h90 : k ≠ 90) :
      t.val.tapes k = s.val.tapes k :=
    (tf.2.2.2.1 k (Or.inr hk) h90).trans (bkeep k hk h88 h89)
  refine ⟨ca + (cb + cc), t, by omega, ea.seq (eb.seq et),
    BankArray.word_of_eq (tf.2.2.2.1 88 (by omega) (by omega)) b88,
    BankArray.word_of_eq (tf.2.2.2.1 89 (by omega) (by omega)) b89, t90,
    RationalAccumulator.blank_of_eq (keep 91 (by omega) (by omega) (by omega) (by omega))
      (emptyPrivate 91 (by simp [Private])),
    RationalAccumulator.blank_of_eq (keep 92 (by omega) (by omega) (by omega) (by omega))
      (emptyPrivate 92 (by simp [Private])), tss, t7, tm.trans (bm.trans am), tc,
    (DoublingPass.Frame.of_except (by simp [Private]) af).trans
      ((DoublingPass.Frame.of_except (by simp [Private]) bf).trans
        (DoublingPass.Frame.of_except (by simp [Private]) tf))⟩

end Maxwell.Cost.ColorPass
