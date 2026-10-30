import Maxwell.Continuum.SourceRoutingZeroFill
import Maxwell.Continuum.SourceRoutingTreeMemory

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def cleanup : List ℕ := [140,141,142]
def code : Code := .seq (NatAssign.code setup)
  (.seq (PositiveGraph.Initialize.fillCode ports) (WordCleanup.code cleanup))

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,i=4 ∨ 10 ≤ i→i≠37→i∉banks→t.tapes i=s.tapes i

theorem executes (q : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hq : ∀i∈controls,(q i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NodeVisit.Clean s.val) (hb : ∀i∈banks,Blank s.val i)
    (hi : ∀i∈controls,RationalAccumulator.Word s.val i (q i)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ 2^30*(q 801+1)*(B+2)^2 ∧
      NodeVisit.Clean t.val ∧ (∀i∈banks,Blank t.val i) ∧
      (∀i∈controls,RationalAccumulator.Word t.val i (q i)) ∧
      (∀p,q 800 ≤ p→p<q 800+q 801→t.val.memory p=false) ∧
      Memory.Frame (q 800) (q 801) s.val.memory t.val.memory ∧ Frame s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,f0⟩:=setup_executes q B hB hq input tape s hs hb hi
  obtain ⟨c1,b,e1,h1,z1,b1,zero1,m1,f1⟩:=fill_executes q B hB hq input tape a z0 b0
  have bounded : WordCleanup.Bounded cleanup B b.val := by
    intro i hi'
    simp only [cleanup,List.mem_cons,List.not_mem_nil,or_false] at hi'
    rcases hi' with rfl|rfl|rfl
    · exact ⟨(1 : ℕ).bits,by simpa using hB,b1 140 (by decide)⟩
    · exact ⟨(q 800).bits,hq 800 (by decide),b1 141 (by decide)⟩
    · exact ⟨(q 801).bits,hq 801 (by decide),b1 142 (by decide)⟩
  obtain ⟨c2,t,e2,h2,zt,f2⟩:=WordCleanup.executes cleanup B input tape b bounded
  have clean : NodeVisit.Clean t.val := by
    apply (Workspace.raw_iff t.val).mpr
    intro i hi'
    have disjoint : Disjoint Workspace.raw cleanup.toFinset := by decide
    exact RationalAccumulator.blank_of_eq (f2.tapes i (Finset.disjoint_left.mp disjoint hi'))
      ((Workspace.raw_iff b.val).mp z1 i hi')
  have blank : ∀i∈banks,Blank t.val i := by
    intro i hi'
    simp only [banks,Finset.mem_insert,Finset.mem_singleton] at hi'
    rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl
    · exact zt 140 (by decide)
    · exact zt 141 (by decide)
    · exact zt 142 (by decide)
    all_goals apply RationalAccumulator.blank_of_eq (f2.tapes _ (by decide))
    all_goals exact (RationalAccumulator.zero_word_iff_blank _ _).mp (b1 _ (by decide))
  have frame : Frame s.val t.val := by
    refine ⟨f2.inputHead.trans (f1.inputHead.trans f0.inputHead),
      f2.randomCursor.trans (f1.randomCursor.trans f0.randomCursor),
      f2.output.trans (f1.output.trans f0.output),?_⟩
    intro i hi' h37 hn
    have b160 : i≠160 := fun he => hn (he ▸ (by decide))
    have b161 : i≠161 := fun he => hn (he ▸ (by decide))
    have b162 : i≠162 := fun he => hn (he ▸ (by decide))
    have ckeep : i∉cleanup.toFinset := by
      have subset : cleanup.toFinset⊆banks := by decide
      exact fun hh => hn (subset hh)
    have skeep : i∉NatAssign.changes setup := by
      have subset : NatAssign.changes setup⊆({0,1,2,3}:Finset ℕ)∪banks := by decide
      intro hh
      rcases Finset.mem_union.mp (subset hh) with hh|hh
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hh;omega
      · exact hn hh
    exact (f2.tapes i ckeep).trans ((f1.tapes i hi' h37 b160 b161 b162).trans (f0.tapes i skeep))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,clean,blank,?_,?_,?_,frame⟩
  · change c1 ≤ 22000*(q 801+1)*(B+2)^2 at h1
    change c2 ≤ 3*(6*B+4)+1 at h2
    have small : B+2 ≤ (q 801+1)*(B+2)^2 := by nlinarith
    have sq : (B+2)^2 ≤ (q 801+1)*(B+2)^2 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith only [h0,h1,h2,small,sq]
  · intro i hi'
    apply RationalAccumulator.word_of_eq (frame.tapes i ?_ ?_ ?_) (hi i hi')
    all_goals simp only [controls,Finset.mem_insert,Finset.mem_singleton] at hi'
    · omega
    · omega
    · simp only [banks,Finset.mem_insert,Finset.mem_singleton];omega
  · intro p hlo hhi
    rw [f2.memory]
    exact zero1 p hlo hhi
  · intro p hp
    exact (congrFun f2.memory p).trans ((m1 p (by simpa only [Nat.mul_one] using hp)).trans (congrFun f0.memory p))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
