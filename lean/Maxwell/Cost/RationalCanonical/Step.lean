import Maxwell.Cost.RationalCanonical.Divide
import Maxwell.Cost.RationalCanonical.Transfer
import Maxwell.Cost.RationalCanonical.Euclid

set_option maxHeartbeats 800000
namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

def stepCode : Code := .seq divideCode <|
  .seq (.call (TapeOps.clear 222)) <|
  .seq (.call (TapeOps.clear 220)) <|
  .seq (.call (WordTransfer.move 221 220)) (.call (WordTransfer.move 223 221))

theorem transferFrame (source target : ℕ) {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t) : DivisionFrame {source,target} s t :=
  ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i hi => h.2.2.2.2.2.1 i (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.1)
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi; exact hi.2),
    fun i _ h24 h25 h26 h27 => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

structure Ready (s : BitRAMState) (a b : ℕ) : Prop where
  first : Word s 220 a
  second : Word s 221 b
  quotient : Blank s 222
  remainder : Blank s 223
  scratch : ∀ i, i < 5 → Blank s i

theorem step (input : List Bool) (tape : ℕ → Bool) (a b : ℕ) (hbpos : 0 < b)
    (s : Store) (hs : Ready s.val a b) :
    ∃ cost t, cost ≤ 2000*(a.bits.length+b.bits.length+2)^2 ∧
      Executes input tape stepCode cost s t ∧ Ready t.val b (a%b) ∧
      DivisionFrame {0,1,2,3,4,220,221,222,223} s.val t.val := by
  obtain ⟨dc,d,hdc,ed,hq,hr,ha,hb,hready,fd⟩ :=
    divide input tape a b hbpos s hs.first hs.second hs.scratch hs.quotient hs.remainder
  obtain ⟨s1,e1,z1,f1⟩ := clear_word 222 (a/b) input tape d hq
  have F1 := transferFrame 222 222 f1
  obtain ⟨s2,e2,z2,f2⟩ := clear_word 220 a input tape s1 (F1.word (by decide) ha)
  have F2 := transferFrame 220 220 f2
  obtain ⟨s3,e3,z3,w3,f3⟩ := move_word 221 220 b (by decide) input tape s2
    (F2.word (by decide) (F1.word (by decide) hb)) z2
  have F3 := transferFrame 221 220 f3
  obtain ⟨t,e4,z4,w4,f4⟩ := move_word 223 221 (a%b) (by decide) input tape s3
    (F3.word (by decide) (F2.word (by decide) (F1.word (by decide) hr))) z3
  have F4 := transferFrame 223 221 f4
  have Ft := F1.trans (F2.trans (F3.trans F4))
  have hscratch : ∀ i, i < 5 → Blank t.val i := by
    intro i hi
    apply Ft.blank _ (hready i hi)
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  have hf : DivisionFrame {0,1,2,3,4,220,221,222,223} s.val t.val := by
    apply (fd.trans Ft).mono
    intro i hi
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto
  refine ⟨dc+((6*(a/b).bits.length+4)+((6*a.bits.length+4)+
    ((12*b.bits.length+11)+(12*(a%b).bits.length+11)))),t,?_,
    ed.seq (e1.seq (e2.seq (e3.seq e4))),
    ⟨F4.word (by decide) w3,w4,?_,(zero_word_iff_blank _ _).mp z4,hscratch⟩,hf⟩
  · have hq' : (a/b).bits.length ≤ a.bits.length := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.div_le_self _ _)
    have hr' : (a%b).bits.length ≤ b.bits.length := by
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.mod_lt a hbpos).le
    nlinarith [Nat.le_self_pow (by decide : (2:ℕ) ≠ 0) (a.bits.length+b.bits.length+2)]
  · exact (F2.trans (F3.trans F4)).blank (by decide) ((zero_word_iff_blank _ _).mp z1)

end Maxwell.Cost.RationalCanonical
