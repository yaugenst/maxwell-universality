import Maxwell.Cost.DoublingPass.ReadOne

namespace Maxwell.Cost.DoublingPass
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

abbrev labelWord (layout : Layout) {n : ℕ} (label : Fin n) : List Bool :=
  IncidenceEncoding.word layout.width label.val

def readCode : Code := .seq (BankArray.readBankCode 80 81 82 83 88)
  (.seq (BankArray.readBankCode 80 88 82 83 89)
  (.seq (BankArray.readBankCode 80 81 84 83 90) (BankArray.readBankCode 80 88 84 83 91)))

/-- Four charged indexed reads share the first saved jump word as the
indirect address for both halves of the doubling computation. -/
theorem read_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved output : State n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2 ^ layout.width)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (s : Store) (cfg : Config layout index clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 140000 * (budget layout index + 1)^2 ∧
      Executes input tape readCode cost s t ∧
      Word t.val 88 (labelWord layout (saved.jump.get j)) ∧
      Word t.val 89 (labelWord layout (saved.jump.get (saved.jump.get j))) ∧
      Word t.val 90 (labelWord layout (saved.minimum.get j)) ∧
      Word t.val 91 (labelWord layout (saved.minimum.get (saved.jump.get j))) ∧
      Blank t.val 92 ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory = s.val.memory ∧ Config layout index clock t.val ∧ Frame s.val t.val := by
  rcases work with ⟨scratch, empty7, emptyPrivate⟩
  obtain ⟨ca, a, hca, ea, a88, ass, a7, am, ac, af⟩ :=
    read_one input tape layout index clock index saved.jump layout.oldJump 81 82 88 j
      (by omega) (by omega) (by simp [Private]) hw hi hc
      (by dsimp [budget]; omega) (by dsimp [budget]; omega) s cfg scratch empty7
      (emptyPrivate 88 (by simp [Private])) cfg.index cfg.oldJump rep.oldJump
  have indirectValue : addressValue (labelWord layout (saved.jump.get j)) = (saved.jump.get j).val :=
    IncidenceEncoding.word_value _ _ (lt_of_lt_of_le (saved.jump.get j).isLt hn)
  obtain ⟨cb, b, hcb, eb, b89, bss, b7, bm, bc, bf⟩ :=
    read_one input tape layout index clock (labelWord layout (saved.jump.get j)) saved.jump
      layout.oldJump 88 82 89 (saved.jump.get j) (by omega) (by omega) (by simp [Private])
      hw indirectValue hc (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega)
      (by dsimp [budget]; omega) a ac ass a7
      (RationalAccumulator.blank_of_eq (af.2.2.2.1 89 (by omega) (by omega))
        (emptyPrivate 89 (by simp [Private]))) a88 ac.oldJump (by simpa [am] using rep.oldJump)
  have bkeep (k : ℕ) (hk : 10 ≤ k) (h88 : k ≠ 88) (h89 : k ≠ 89) : b.val.tapes k = s.val.tapes k :=
    (bf.2.2.2.1 k (Or.inr hk) h89).trans (af.2.2.2.1 k (Or.inr hk) h88)
  obtain ⟨cc, c, hcc, ec, c90, css, c7, cm, cfgC, cf⟩ :=
    read_one input tape layout index clock index saved.minimum layout.oldMinimum 81 84 90 j
      (by omega) (by omega) (by simp [Private]) hw hi hc
      (by dsimp [budget]; omega) (by dsimp [budget]; omega) b bc bss b7
      (RationalAccumulator.blank_of_eq (bkeep 90 (by omega) (by omega) (by omega))
        (emptyPrivate 90 (by simp [Private]))) bc.index bc.oldMinimum
      (by simpa [bm, am] using rep.oldMinimum)
  have c88 : Word c.val 88 (labelWord layout (saved.jump.get j)) := BankArray.word_of_eq
    ((cf.2.2.2.1 88 (by omega) (by omega)).trans (bf.2.2.2.1 88 (by omega) (by omega))) a88
  have ckeep (k : ℕ) (hk : 10 ≤ k) (h88 : k ≠ 88) (h89 : k ≠ 89) (h90 : k ≠ 90) :
      c.val.tapes k = s.val.tapes k :=
    (cf.2.2.2.1 k (Or.inr hk) h90).trans (bkeep k hk h88 h89)
  obtain ⟨cd, t, hcd, et, t91, tss, t7, tm, tc, tf⟩ :=
    read_one input tape layout index clock (labelWord layout (saved.jump.get j)) saved.minimum
      layout.oldMinimum 88 84 91 (saved.jump.get j) (by omega) (by omega) (by simp [Private])
      hw indirectValue hc (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega)
      (by dsimp [budget]; omega) c cfgC css c7
      (RationalAccumulator.blank_of_eq (ckeep 91 (by omega) (by omega) (by omega) (by omega))
        (emptyPrivate 91 (by simp [Private]))) c88 cfgC.oldMinimum
      (by simpa [cm, bm, am] using rep.oldMinimum)
  refine ⟨ca + (cb + (cc + cd)), t, by omega, ea.seq (eb.seq (ec.seq et)),
    BankArray.word_of_eq (tf.2.2.2.1 88 (by omega) (by omega)) c88,
    BankArray.word_of_eq ((tf.2.2.2.1 89 (by omega) (by omega)).trans
      (cf.2.2.2.1 89 (by omega) (by omega))) b89,
    BankArray.word_of_eq (tf.2.2.2.1 90 (by omega) (by omega)) c90,
    t91, RationalAccumulator.blank_of_eq
      ((tf.2.2.2.1 92 (by omega) (by omega)).trans
        (ckeep 92 (by omega) (by omega) (by omega) (by omega))) (emptyPrivate 92 (by simp [Private])),
    tss, t7, tm.trans (cm.trans (bm.trans am)), tc,
    (Frame.of_except (by simp [Private]) af).trans
      ((Frame.of_except (by simp [Private]) bf).trans
        ((Frame.of_except (by simp [Private]) cf).trans (Frame.of_except (by simp [Private]) tf)))⟩

end Maxwell.Cost.DoublingPass
