import Maxwell.Cost.ConjugatePass.Encoding
import Maxwell.Cost.DoublingPass.Read

namespace Maxwell.Cost.ConjugatePass
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

def readCode : Code := .seq (BankArray.readBankCode 80 81 82 83 88)
  (.seq (BankArray.readBankCode 80 88 84 83 89) (BankArray.readBankCode 80 89 85 83 90))

/-- Three indirect reads construct the target-conjugated pairing at one slot. -/
theorem read_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (saved : Tables n) (output : Vector (List Bool) n) (j : Fin n) (index clock : List Bool)
    (hw : 0 < layout.width) (hn : n ≤ 2^layout.width)
    (hi : addressValue index = j.val) (hc : clock.length = layout.width)
    (s : Store) (cfg : Config layout index clock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory saved output) :
    ∃ cost t, cost ≤ 105000*(budget layout index+1)^2 ∧ Executes input tape readCode cost s t ∧
      Word t.val 88 (labelWord layout (saved.forward.get j)) ∧
      Word t.val 89 (labelWord layout (saved.pairing.get (saved.forward.get j))) ∧
      Word t.val 90 (labelWord layout (value saved j)) ∧
      Blank t.val 91 ∧ Blank t.val 92 ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ Config layout index clock t.val ∧ Frame s.val t.val := by
  rcases work with ⟨scratch,empty7,empty⟩
  obtain ⟨ca,a,hca,ea,a88,ass,a7,am,ac,af⟩ := read_one input tape layout index clock index saved.forward
    layout.oldJump 81 82 88 j (by omega) (by omega) (by simp [Private]) hw hi hc
    (by dsimp [budget]; omega) (by dsimp [budget]; omega) s cfg scratch empty7
    (empty 88 (by simp [Private])) cfg.index cfg.oldJump rep.forward
  obtain ⟨cb,b,hcb,eb,b89,bss,b7,bm,bc,bf⟩ := read_one input tape layout index clock
    (labelWord layout (saved.forward.get j)) saved.pairing layout.oldMinimum 88 84 89 (saved.forward.get j)
    (by omega) (by omega) (by simp [Private]) hw
    (IncidenceEncoding.word_value _ _ ((saved.forward.get j).isLt.trans_le hn)) hc
    (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega)
    (by dsimp [budget]; omega) a ac ass a7
    (RationalAccumulator.blank_of_eq (af.2.2.2.1 89 (by omega) (by omega)) (empty 89 (by simp [Private])))
    a88 ac.oldMinimum (by simpa only [am] using rep.pairing)
  have keepB (k : ℕ) (hk : 10 ≤ k) (h88 : k≠88) (h89 : k≠89) : b.val.tapes k=s.val.tapes k :=
    (bf.2.2.2.1 k (Or.inr hk) h89).trans (af.2.2.2.1 k (Or.inr hk) h88)
  obtain ⟨cc,t,hcc,ec,t90,tss,t7,tm,tc,tf⟩ := read_one input tape layout index clock
    (labelWord layout (saved.pairing.get (saved.forward.get j))) saved.backward layout.newJump 89 85 90
    (saved.pairing.get (saved.forward.get j)) (by omega) (by omega) (by simp [Private]) hw
    (IncidenceEncoding.word_value _ _ ((saved.pairing.get (saved.forward.get j)).isLt.trans_le hn)) hc
    (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega)
    (by dsimp [budget]; omega) b bc bss b7
    (RationalAccumulator.blank_of_eq (keepB 90 (by omega) (by omega) (by omega)) (empty 90 (by simp [Private])))
    b89 bc.newJump (by simpa only [bm,am] using rep.backward)
  refine ⟨ca+(cb+cc),t,by omega,ea.seq (eb.seq ec),
    BankArray.word_of_eq ((tf.2.2.2.1 88 (by omega) (by omega)).trans (bf.2.2.2.1 88 (by omega) (by omega))) a88,
    BankArray.word_of_eq (tf.2.2.2.1 89 (by omega) (by omega)) b89,t90,?_,?_,tss,t7,
    tm.trans (bm.trans am),tc,(Frame.of_except (by simp [Private]) af).trans
      ((Frame.of_except (by simp [Private]) bf).trans (Frame.of_except (by simp [Private]) tf))⟩
  · exact RationalAccumulator.blank_of_eq ((tf.2.2.2.1 91 (by omega) (by omega)).trans
      (keepB 91 (by omega) (by omega) (by omega))) (empty 91 (by simp [Private]))
  · exact RationalAccumulator.blank_of_eq ((tf.2.2.2.1 92 (by omega) (by omega)).trans
      (keepB 92 (by omega) (by omega) (by omega))) (empty 92 (by simp [Private]))

end Maxwell.Cost.ConjugatePass
