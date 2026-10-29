import Maxwell.Cost.PhysicalEmit.For

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator

def recordPrefix (records : ℕ → List Bool) (n : ℕ) : List Bool :=
  (List.range n).flatMap records

@[simp] theorem recordPrefix_zero (records : ℕ → List Bool) : recordPrefix records 0 = [] := rfl

theorem recordPrefix_succ (records : ℕ → List Bool) (n : ℕ) :
    recordPrefix records (n+1) = recordPrefix records n ++ records n := by
  simp [recordPrefix,List.range_succ]

/-- Each record is produced by the same finite body from its actual stored
coordinate. This theorem records the exact serialization order. -/
theorem for_records (dimension count index N : ℕ)
    (hci : count ≠ index) (hdc : dimension ≠ count) (hdi : dimension ≠ index) (body : Code)
    (input : List Bool) (tape : ℕ → Bool) (R : Store → Prop)
    (records : ℕ → List Bool) (Q : ℕ)
    (stable : ∀ s t, LoopFrame {count,index} s.val t.val → R s → R t)
    (bodyCorrect : ∀ i, i < N → ∀ s, R s → Word s.val index i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ R t ∧
        t.val.output = (records i).reverse ++ s.val.output ∧
        t.val.tapes index = s.val.tapes index ∧ t.val.tapes count = s.val.tapes count)
    (oldIndex : ℕ) (oldCount : List Bool) (s : Store)
    (hd : Word s.val dimension N) (hc : BankArray.Word s.val count oldCount)
    (hi : Word s.val index oldIndex) (hs : R s) :
    ∃ cost t finalWord,
      cost ≤ 6*oldIndex.bits.length+6*oldCount.length+15*N.bits.length+25+
        (N+1)*(13*N.bits.length+15)+N*(Q+12*N.bits.length+18) ∧
      Executes input tape (forCode dimension count index body) cost s t ∧ R t ∧
      t.val.output = (recordPrefix records N).reverse ++ s.val.output ∧
      Word t.val index N ∧ BankArray.Word t.val count finalWord ∧ finalWord.length = N.bits.length := by
  let P : ℕ → Store → Prop := fun i t => R t ∧ t.val.output = (recordPrefix records i).reverse ++ s.val.output
  have hstable : ∀ i s t, LoopFrame {count,index} s.val t.val → P i s → P i t := by
    intro i s t hf hP
    exact ⟨stable s t hf hP.1,hf.output.trans hP.2⟩
  have hbody : ∀ i, i < N → ∀ u, P i u → Word u.val index i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost u t ∧ P (i+1) t ∧
        t.val.tapes index = u.val.tapes index ∧ t.val.tapes count = u.val.tapes count := by
    intro i hi u hP hw
    obtain ⟨c,t,hc,he,hR,ho,hidx,hcount⟩ := bodyCorrect i hi u hP.1 hw
    refine ⟨c,t,hc,he,⟨hR,?_⟩,hidx,hcount⟩
    rw [ho,hP.2,recordPrefix_succ,List.reverse_append,List.append_assoc]
  obtain ⟨c,t,word,hc,he,hP,hi,hcount,hlen⟩ := for_executes dimension count index N hci hdc hdi body
    input tape P Q hstable hbody oldIndex oldCount s hd hc hi ⟨hs,by simp⟩
  exact ⟨c,t,word,hc,he,hP.1,hP.2,hi,hcount,hlen⟩

end Maxwell.Cost.PhysicalEmit
