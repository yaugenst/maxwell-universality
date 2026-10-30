import Maxwell.Cost.PowerOfTwo
import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.BankArray.Read

/-! A runtime binary width drives the literal construction of a unary
array clock. Every written bit and the replacement of the old clock is
charged. The code is independent of the width. -/

namespace Maxwell.Continuum.Calibration.WidthClock

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def core (counter target : ℕ) : Code := Counted.code counter (PowerOfTwo.appendBit target false)

theorem core_executes (counter target : ℕ) (hne : counter ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (co targetOrigin : ℤ) (s : Store)
    (hc : s.val.tapes counter=BitTape.shifted xs co)
    (ht : s.val.tapes target={BitTape.blank with head:=targetOrigin}) :
    ∃ cost t finalCounter, Executes input tape (core counter target) cost s t ∧
      cost ≤ (addressValue xs+1)*(13*xs.length+21) ∧
      t.val.tapes counter=BitTape.shifted finalCounter co ∧ finalCounter.length=xs.length ∧
      t.val.tapes target=BitTape.shiftedEnd (List.replicate (addressValue xs) false) targetOrigin ∧
      PowerOfTwo.Frame counter target s t := by
  let N := addressValue xs
  let inv (n : ℕ) (t : Store) : Prop := n ≤ N ∧
    t.val.tapes target=BitTape.shiftedEnd (List.replicate (N-n) false) targetOrigin ∧
    PowerOfTwo.Frame counter target s t
  have stable : ∀ n a b, Counted.Frame counter a b → inv n a → inv n b := by
    intro n a b hf hi
    exact ⟨hi.1,(hf.2.2.2.2.2.1 target (Ne.symm hne)).trans hi.2.1,
      hi.2.2.trans (PowerOfTwo.frame_of_test hf)⟩
  have body : ∀ n word a, inv (n+1) a →
      a.val.tapes counter=BitTape.shifted word co → addressValue word=n →
      ∃ c b, Executes input tape (PowerOfTwo.appendBit target false) c a b ∧ inv n b ∧
        b.val.tapes counter=BitTape.shifted word co ∧ c ≤ 6 := by
    intro n word a hi hword _
    refine ⟨6,PowerOfTwo.appendState target false a,PowerOfTwo.append_executes _ _ _ _ _,
      ⟨by omega,?_,hi.2.2.trans (PowerOfTwo.append_frame counter target false a)⟩,?_,le_rfl⟩
    · rw [PowerOfTwo.append_word target false a _ targetOrigin hi.2.1]
      have hn : N-n=(N-(n+1))+1 := by omega
      rw [hn,List.replicate_add]
      rfl
    · simpa [PowerOfTwo.appendState,Store.ofState,hne] using hword
  obtain ⟨cost,t,word,e,hi,hw,hl,_,hcost⟩ := CountedShifted.executes counter co
    (PowerOfTwo.appendBit target false) input tape inv (fun _ => 6) stable body N xs s rfl hc
    ⟨le_rfl,by simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.blank] using ht,
      PowerOfTwo.Frame.refl _ _ _⟩
  refine ⟨cost,t,word,e,?_,hw,hl,?_,hi.2.2⟩
  · simp at hcost
    dsimp only [N] at hcost
    nlinarith only [hcost]
  · simpa only [Nat.sub_zero] using hi.2.1

def code (source counter target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source counter))
    (.seq (core counter target)
      (.seq (.call (TapeOps.clear counter)) (.call (Rewind.program target))))

theorem executes (source counter target : ℕ)
    (hsc : source ≠ counter) (hst : source ≠ target) (hct : counter ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hs : BankArray.Word s.val source xs) (hc : Blank s.val counter) (ht : Blank s.val target) :
    ∃ cost t, Executes input tape (code source counter target) cost s t ∧
      cost ≤ (addressValue xs+1)*(13*xs.length+21)+21*xs.length+4*addressValue xs+31 ∧
      BankArray.Word t.val source xs ∧ Blank t.val counter ∧
      BankArray.Word t.val target (List.replicate (addressValue xs) false) ∧
      BinaryPrecision.Frame {counter,target} s.val t.val := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨co,hc⟩ := hc
  obtain ⟨targetOrigin,ht⟩ := ht
  obtain ⟨cloned,hclone,hpc,hsource,hcounter,hf0⟩ := WordTransfer.clone_steps source counter hsc
    input tape xs so co s.val s.property hs hc
  let u := Store.ofState cloned
  have e0 : Executes input tape (.call (WordTransfer.clone source counter)) (15*xs.length+17) s u := by
    simpa using Executes.call _ s cloned _ hclone (by rw [hpc]; rfl)
  have f0 : BinaryPrecision.Frame {counter,target} s.val u.val := by
    refine ⟨hf0.1,hf0.2.1,hf0.2.2.1,hf0.2.2.2.1,hf0.2.2.2.2.1,?_⟩
    intro i hi
    have hic : i ≠ counter := fun he => hi (by simp [he])
    by_cases his : i=source
    · subst i
      exact hsource.trans hs.symm
    · exact hf0.2.2.2.2.2.1 i his hic
  have htu : u.val.tapes target={BitTape.blank with head:=targetOrigin} :=
    (hf0.2.2.2.2.2.1 target (Ne.symm hst) (Ne.symm hct)).trans ht
  obtain ⟨c1,u1,word,e1,hc1,count1,len1,target1,hf1⟩ :=
    core_executes counter target hct input tape xs co targetOrigin u hcounter htu
  have f1 : BinaryPrecision.Frame {counter,target} u.val u1.val := by
    refine ⟨hf1.1,hf1.2.1,hf1.2.2.1,hf1.2.2.2.1,hf1.2.2.2.2.1,?_⟩
    intro i hi
    have hi' : i ≠ counter ∧ i ≠ target := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
    exact hf1.2.2.2.2.2.1 i hi'.1 hi'.2
  obtain ⟨cleared,hclear,hpc2,blank2,hf2⟩ := TapeOps.clear_steps counter input tape word co
    u1.val u1.property count1
  let u2 := Store.ofState cleared
  have e2 : Executes input tape (.call (TapeOps.clear counter)) (6*word.length+4) u1 u2 := by
    simpa using Executes.call _ u1 cleared _ hclear (by rw [hpc2]; rfl)
  have target2 : u2.val.tapes target=BitTape.shiftedEnd (List.replicate (addressValue xs) false) targetOrigin :=
    (hf2.2.2.2.2.2.1 target (Ne.symm hct) (Ne.symm hct)).trans target1
  have hr := WordTransfer.rewind_shifted target targetOrigin input tape
    (List.replicate (addressValue xs) false) u2.val u2.property target2
  let t := Store.ofState (Rewind.finishAt target targetOrigin u2.val)
  have e3 : Executes input tape (.call (Rewind.program target)) (4*addressValue xs+6) u2 t := by
    simpa only [List.length_replicate] using
      Executes.call _ u2 _ _ hr.1 (by simp [Rewind.program,Rewind.finishAt])
  have hf3 := WordTransfer.frame_rewind target target target (Or.inl rfl) targetOrigin u2.val
  have f2 : BinaryPrecision.Frame {counter,target} u1.val u2.val := by
    refine ⟨hf2.1,hf2.2.1,hf2.2.2.1,hf2.2.2.2.1,hf2.2.2.2.2.1,?_⟩
    intro i hi
    have hic : i ≠ counter := fun he => hi (by simp [he])
    exact hf2.2.2.2.2.2.1 i hic hic
  have f3 : BinaryPrecision.Frame {counter,target} u2.val t.val := by
    refine ⟨hf3.1,hf3.2.1,hf3.2.2.1,hf3.2.2.2.1,hf3.2.2.2.2.1,?_⟩
    intro i hi
    have hit : i ≠ target := fun he => hi (by simp [he])
    exact hf3.2.2.2.2.2.1 i hit hit
  have frame := f0.trans (f1.trans (f2.trans f3))
  refine ⟨(15*xs.length+17)+(c1+((6*word.length+4)+(4*addressValue xs+6))),t,
    e0.seq (e1.seq (e2.seq e3)),?_,?_,?_,⟨targetOrigin,hr.2⟩,frame⟩
  · rw [len1]
    omega
  · exact ⟨so,(frame.tapes source (by simp [hsc,hst])).trans hs⟩
  · exact ⟨co+word.length,(hf3.2.2.2.2.2.1 counter hct hct).trans blank2⟩

#print axioms executes

end Maxwell.Continuum.Calibration.WidthClock
