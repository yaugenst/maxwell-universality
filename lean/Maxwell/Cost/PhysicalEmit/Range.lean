import Maxwell.Cost.PhysicalEmit.Increment

namespace Maxwell.Cost.PhysicalEmit
open Structured RationalAccumulator
open scoped BigOperators

def rangeCode (count index : ℕ) (body : Code) : Code :=
  CountedShifted.code count (.seq body (incrementCode index))

/-- An actual increasing-coordinate traversal. The count is an ordinary
binary tape, and the body is one fixed finite code fragment. -/
theorem range (count index N : ℕ) (hne : count ≠ index) (body : Code)
    (input : List Bool) (tape : ℕ → Bool) (P : ℕ → Store → Prop) (Q : ℕ)
    (stable : ∀ k s t, LoopFrame {count,index} s.val t.val → P k s → P k t)
    (bodyCorrect : ∀ i, i < N → ∀ s, P i s → Word s.val index i →
      ∃ cost t, cost ≤ Q ∧ Executes input tape body cost s t ∧ P (i+1) t ∧
        t.val.tapes index = s.val.tapes index ∧ t.val.tapes count = s.val.tapes count)
    (origin : ℤ) (xs : List Bool) (s : Store) (hxs : addressValue xs = N)
    (hc : s.val.tapes count = BitTape.shifted xs origin)
    (hi : Word s.val index 0) (hs : P 0 s) :
    ∃ cost t finalWord,
      cost ≤ (N+1)*(13*xs.length+15)+N*(Q+12*N.bits.length+18) ∧
      Executes input tape (rangeCode count index body) cost s t ∧
      P N t ∧ Word t.val index N ∧
      t.val.tapes count = BitTape.shifted finalWord origin ∧ finalWord.length = xs.length := by
  let invariant : ℕ → Store → Prop := fun n s => n ≤ N ∧ P (N-n) s ∧ Word s.val index (N-n)
  have hstable : ∀ n s t, CountedShifted.Frame count s t → invariant n s → invariant n t := by
    intro n s t hf hn
    refine ⟨hn.1,stable (N-n) s t ((LoopFrame.ofCounted hf).mono (by simp)) hn.2.1,?_⟩
    exact word_of_eq (hf.2.2.2.2.2.1 index (Ne.symm hne)) hn.2.2
  have hbody : ∀ n xs s, invariant (n+1) s →
      s.val.tapes count = BitTape.shifted xs origin → addressValue xs = n →
      ∃ cost t, Executes input tape (.seq body (incrementCode index)) cost s t ∧
        invariant n t ∧ t.val.tapes count = BitTape.shifted xs origin ∧
        cost ≤ Q+12*N.bits.length+18 := by
    intro n ys s hn hsCount _
    have hil : N-(n+1) < N := by omega
    have hisucc : N-(n+1)+1 = N-n := by omega
    obtain ⟨c,u,hcu,eu,hu,hiu,hcountu⟩ := bodyCorrect (N-(n+1)) hil s hn.2.1 hn.2.2
    obtain ⟨d,t,hdt,et,hit,ft⟩ := increment index (N-(n+1)) input tape u
      (word_of_eq hiu hn.2.2)
    have hnt : P (N-n) t := by
      rw [← hisucc]
      apply stable _ u t (ft.mono (by simp)) hu
    have hlen : (N-(n+1)).bits.length ≤ N.bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.sub_le _ _)
    refine ⟨c+d,t,eu.seq et,⟨by omega,hnt,by simpa only [hisucc] using hit⟩,?_,by omega⟩
    exact (ft.tapes count (by simpa using hne)).trans (hcountu.trans hsCount)
  obtain ⟨cost,t,word,he,hP,hw,hlen,_,hcost⟩ := CountedShifted.executes count origin
    (.seq body (incrementCode index)) input tape invariant (fun _ => Q+12*N.bits.length+18)
    hstable hbody N xs s hxs hc ⟨le_refl _,by simpa using hs,by simpa using hi⟩
  refine ⟨cost,t,word,?_,he,?_,?_,hw,hlen⟩
  · simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using hcost
  · simpa [invariant] using hP.2.1
  · simpa [invariant] using hP.2.2

end Maxwell.Cost.PhysicalEmit
