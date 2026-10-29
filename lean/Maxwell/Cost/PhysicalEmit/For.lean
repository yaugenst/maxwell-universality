import Maxwell.Cost.PhysicalEmit.Range
import Maxwell.Cost.WordReplace

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

theorem LoopFrame.ofTransfer {source target : ℕ} {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t) : LoopFrame {source,target} s t :=
  ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.1)
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.2),
    fun i _ h24 h25 h26 h27 _ _ => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

theorem LoopFrame.ofReplace {target : ℕ} {s t : BitRAMState}
    (h : WordReplace.Frame target s t) : LoopFrame {target} s t :=
  ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by simpa using hi),
    fun i _ h24 h25 h26 h27 _ _ => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

/-- Reset an actual coordinate, copy an actual dimension into its private
countdown, then traverse its integer coordinates in increasing order. -/
def forCode (dimension count index : ℕ) (body : Code) : Code :=
  .seq (.call (TapeOps.clear index)) <|
  .seq (WordReplace.code dimension count) (rangeCode count index body)

theorem for_executes (dimension count index N : ℕ)
    (hci : count ≠ index) (hdc : dimension ≠ count) (hdi : dimension ≠ index) (body : Code)
    (input : List Bool) (tape : ℕ → Bool) (P : ℕ → Store → Prop) (Q : ℕ)
    (stable : ∀ k s t, LoopFrame {count,index} s.val t.val → P k s → P k t)
    (bodyCorrect : ∀ i, i < N → ∀ s, P i s → Word s.val index i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ P (i+1) t ∧
        t.val.tapes index = s.val.tapes index ∧ t.val.tapes count = s.val.tapes count)
    (oldIndex : ℕ) (oldCount : List Bool) (s : Store)
    (hd : Word s.val dimension N) (hc : BankArray.Word s.val count oldCount)
    (hi : Word s.val index oldIndex) (hs : P 0 s) :
    ∃ cost t finalWord,
      cost ≤ 6*oldIndex.bits.length+6*oldCount.length+15*N.bits.length+25+
        (N+1)*(13*N.bits.length+15)+N*(Q+12*N.bits.length+18) ∧
      Executes input tape (forCode dimension count index body) cost s t ∧
      P N t ∧ Word t.val index N ∧ BankArray.Word t.val count finalWord ∧
      finalWord.length = N.bits.length := by
  obtain ⟨u,e1,z1,f1⟩ := RationalCanonical.clear_word index oldIndex input tape s hi
  have F1 := LoopFrame.ofTransfer f1
  have hu : P 0 u := stable 0 s u (F1.mono (by simp)) hs
  have hdu : Word u.val dimension N := word_of_eq
    (F1.tapes dimension (by simpa using hdi)) hd
  have hcu : BankArray.Word u.val count oldCount := BankArray.word_of_eq
    (F1.tapes count (by simpa using hci)) hc
  obtain ⟨v,e2,w2,f2⟩ := WordReplace.executes dimension count hdc input tape N.bits oldCount u hdu hcu
  have F2 := LoopFrame.ofReplace f2
  have hv : P 0 v := stable 0 u v (F2.mono (by simp)) hu
  obtain ⟨origin,w2⟩ := w2
  obtain ⟨c,t,word,hct,e3,pt,it,ct,lt⟩ := range count index N hci body input tape P Q stable bodyCorrect
    origin N.bits v (address_bits N) w2
    (word_of_eq (F2.tapes index (by simpa using Ne.symm hci)) z1) hv
  refine ⟨(6*oldIndex.bits.length+4)+((6*oldCount.length+15*N.bits.length+21)+c),
    t,word,by omega,e1.seq (e2.seq e3),pt,it,⟨origin,ct⟩,lt⟩

end Maxwell.Cost.PhysicalEmit
