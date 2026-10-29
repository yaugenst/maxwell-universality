import Maxwell.Cost.RationalCanonical.Loop

set_option maxHeartbeats 800000
namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

def quotientCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source 220)) <|
  .seq divideCode <|
  .seq (.call (TapeOps.clear 220)) (.call (WordTransfer.move 222 target))

/-- Exact division by a stored positive factor. The finite division loop is
executed even when divisibility is known mathematically. -/
theorem quotient (source target a g : ℕ)
    (hsource : 223 < source) (htarget : 223 < target) (hne : source ≠ target)
    (hg : 0 < g) (hdiv : g ∣ a) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : Word s.val source a) (hr : Ready s.val 0 g) (ht : Blank s.val target) :
    ∃ cost t, cost ≤ 2000*(a.bits.length+g.bits.length+2)^2 ∧
      Executes input tape (quotientCode source target) cost s t ∧
      Word t.val target (a/g) ∧ Word t.val source a ∧ Ready t.val 0 g ∧
      DivisionFrame {0,1,2,3,4,220,222,223,source,target} s.val t.val := by
  obtain ⟨u,e1,h1,w1,f1⟩ := clone_word source 220 a (by omega) input tape s ha hr.first
  have F1 := transferFrame source 220 f1
  have hu : Ready u.val a g :=
    ⟨w1,F1.word (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) hr.second,
      F1.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) hr.quotient,
      F1.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) hr.remainder,
      fun i hi => F1.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) (hr.scratch i hi)⟩
  obtain ⟨c,v,hc,e2,q2,r2,a2,g2,s2,f2⟩ :=
    divide input tape a g hg u hu.first hu.second hu.scratch hu.quotient hu.remainder
  obtain ⟨w,e3,z3,f3⟩ := clear_word 220 a input tape v a2
  have F3 := transferFrame 220 220 f3
  obtain ⟨t,e4,z4,q4,f4⟩ := move_word 222 target (a/g) (by omega) input tape w
    (F3.word (by decide) q2)
    ((zero_word_iff_blank _ _).mpr (F3.blank
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega)
      (f2.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega)
      (F1.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) ht))))
  have F4 := transferFrame 222 target f4
  have ff : DivisionFrame {0,1,2,3,4,220,222,223,source,target} s.val t.val := by
    apply (F1.trans (f2.trans (F3.trans F4))).mono
    intro i hi
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto
  refine ⟨(15*a.bits.length+17)+(c+((6*a.bits.length+4)+(12*(a/g).bits.length+11))),t,?_,
    e1.seq (e2.seq (e3.seq e4)),q4,?_,?_,ff⟩
  · have hq : (a/g).bits.length ≤ a.bits.length := by
      rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.div_le_self _ _)
    nlinarith [Nat.le_self_pow (by decide : (2:ℕ) ≠ 0) (a.bits.length+g.bits.length+2)]
  · exact (f2.trans (F3.trans F4)).word
      (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega) h1
  · refine ⟨F4.word (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) z3,
      (F3.trans F4).word (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega) g2,
      (zero_word_iff_blank _ _).mp z4,?_,?_⟩
    · apply (F3.trans F4).blank (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)
      apply (zero_word_iff_blank _ _).mp
      simpa only [Nat.mod_eq_zero_of_dvd hdiv] using r2
    · intro i hi
      exact (F3.trans F4).blank
        (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega) (s2 i hi)

end Maxwell.Cost.RationalCanonical
