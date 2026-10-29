import Maxwell.Cost.ChildPermutation.Common

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def prepareClockCode : Code := .seq (.call (WordTransfer.clone 83 121)) (WordReduceHalf.code 121)

/-- The actual saved parent clock is copied and shortened by one cell.
Its bit values are irrelevant; every other persistent tape is preserved. -/
theorem prepare_clock_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (clock : List Bool) (hc : clock.length=k+2) (s : Store)
    (h83 : Word s.val 83 clock) (h121 : Blank s.val 121) :
    ∃ cost t childClock, cost ≤ 30*(clock.length+1) ∧
      Executes input tape prepareClockCode cost s t ∧
      Word t.val 121 childClock ∧ childClock.length=k+1 ∧ Word t.val 83 clock ∧
      WordTransfer.Frame 121 121 s.val t.val := by
  obtain ⟨po,hpo⟩ := h83
  obtain ⟨co,hco⟩ := h121
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 83 121 (by omega) input tape clock po co s hpo hco
  have htake : (clock.take k).length=k := by simp [List.length_take,hc]
  have hdrop : (clock.drop k).length=2 := by simp [List.length_drop,hc]
  obtain ⟨b,last,hd⟩ := List.length_eq_two.mp hdrop
  have heq : clock=clock.take k++[b,last] := by rw [← hd,List.take_append_drop]
  have ac : a.val.tapes 121=BitTape.shifted (clock.take k++[b,last]) co := by
    rw [← heq]
    simp [atapes]
  obtain ⟨t,et,tc,tf⟩ := WordReduceHalf.executes 121 input tape (clock.take k) b last co a ac
  have frameA : WordTransfer.Frame 121 121 s.val a.val :=
    ⟨af.1,af.2.1,af.2.2.1,af.2.2.2.1,af.2.2.2.2.1,
      fun i hi _ => by simp [atapes,hi],af.2.2.2.2.2.2⟩
  have frame := frameA.trans tf
  refine ⟨15*clock.length+17+(9*(clock.take k).length+31),t,clock.take k++[false],?_,
    ea.seq et,⟨co,tc⟩,by simp [htake],?_,frame⟩
  · rw [htake,hc]
    omega
  · exact BankArray.word_of_eq (frame.2.2.2.2.2.1 83 (by omega) (by omega)) ⟨po,hpo⟩

end Maxwell.Cost.ChildPermutation
