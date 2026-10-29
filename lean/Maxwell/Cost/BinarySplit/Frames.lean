import Maxwell.Cost.BinarySplit.Adapters

namespace Maxwell.Cost.BinarySplit

/-- A split writes the two pairing tables and four ping-pong buffers only. -/
def Outside (layout : Layout) (n p : ℕ) : Prop :=
  (p<layout.pairing ∨ layout.pairing+n*layout.route.width≤p) ∧
  (p<layout.conjugated ∨ layout.conjugated+n*layout.route.width≤p) ∧
  DoublingPass.Outside layout.route n p

def MemoryFrame (layout : Layout) (n : ℕ) (before after : ℕ → Bool) : Prop :=
  ∀ p, Outside layout n p → after p=before p

theorem MemoryFrame.trans {layout : Layout} {n : ℕ} {a b c : ℕ → Bool}
    (h : MemoryFrame layout n a b) (k : MemoryFrame layout n b c) : MemoryFrame layout n a c :=
  fun p hp => (k p hp).trans (h p hp)

theorem MemoryFrame.of_eq {layout : Layout} {n : ℕ} {a b : ℕ → Bool} (h : b=a) : MemoryFrame layout n a b :=
  fun p _ => congrFun h p

theorem MemoryFrame.of_half {layout : Layout} {k : ℕ} {a b : ℕ → Bool}
    (h : HalfPair.MemoryFrame layout.half k a b) : MemoryFrame layout (2*(2^k)) a b :=
  fun p hp => h p hp.1

theorem MemoryFrame.of_conjugate {layout : Layout} {n : ℕ} {a b : ℕ → Bool}
    (h : ConjugatePass.MemoryFrame layout.conjugate n a b) : MemoryFrame layout n a b :=
  fun p hp => h p hp.2.1

theorem MemoryFrame.of_cycle {layout : Layout} {n : ℕ} {a b : ℕ → Bool}
    (h : DoublingPass.MemoryFrame layout.route n a b) : MemoryFrame layout n a b :=
  fun p hp => h p hp.2.2

theorem saved_of_tapes {layout : Layout} {s t : BitRAMState}
    (keep : ∀ i, 100 ≤ i → i ≤ 105 → t.tapes i=s.tapes i) (h : Saved layout s) : Saved layout t :=
  ⟨BankArray.word_of_eq (keep 100 (by omega) (by omega)) h.1,
   BankArray.word_of_eq (keep 101 (by omega) (by omega)) h.2.1,
   BankArray.word_of_eq (keep 102 (by omega) (by omega)) h.2.2.1,
   BankArray.word_of_eq (keep 103 (by omega) (by omega)) h.2.2.2.1,
   BankArray.word_of_eq (keep 104 (by omega) (by omega)) h.2.2.2.2.1,
   BankArray.word_of_eq (keep 105 (by omega) (by omega)) h.2.2.2.2.2⟩

theorem cycle_keep {s t : BitRAMState} (h : CycleSplit.Frame s t) (i : ℕ) (hi : 98 ≤ i) :
    t.tapes i=s.tapes i :=
  h.2.2.2.1 i (by omega) (by simp only [DoublingPass.RoundPrivate,DoublingPass.Private]; omega)
    (by omega) (by omega)

theorem saved_of_cycle {layout : Layout} {s t : BitRAMState} (h : CycleSplit.Frame s t)
    (saved : Saved layout s) : Saved layout t := saved_of_tapes (fun i hi _ => cycle_keep h i (by omega)) saved

theorem init_keep {s t : BitRAMState} (h : DoublingInit.LoopFrame s t) (i : ℕ) (hi : 95 ≤ i) :
    t.tapes i=s.tapes i :=
  h.2.2.2.1 i (by omega) (by omega) (by simp only [DoublingInit.Private,DoublingPass.Private]; omega) (by omega)

theorem conjugate_keep {s t : BitRAMState} (h : DoublingPass.LoopFrame s t) (i : ℕ) (hi : 95 ≤ i) :
    t.tapes i=s.tapes i :=
  h.2.2.2.1 i (by omega) (by omega) (by simp only [DoublingPass.Private]; omega) (by omega)

end Maxwell.Cost.BinarySplit
