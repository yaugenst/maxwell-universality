import Maxwell.Continuum.SourceRoutingTreeStartupFacts

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (NatAssign.code Prepare.instructions) (.seq Depth.code (.seq Power.code Allocation.code))
def work : Finset ℕ := SourceArithmetic.work∪Allocation.work∪{830,813}
def cost (total forward backward : ℕ) : ℕ :=
  3000*8^19*(bits total forward backward+2)^2+2^110*(stageBits total forward backward+2)^2+
    (total+1)*(13*total.bits.length+25)+21*total.bits.length+27+
    Allocation.cost (powered total forward backward) (stageBits total forward backward)

theorem executes (total forward backward : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank SourceArithmetic.ids (seed total forward backward) s.val)
    (hz : PrivateVisit.Clean s) (he : PrivateZero.Clean s)
    (h839 : Blank s.val 839) (h830 : Blank s.val 830) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost total forward backward ∧
      NatAssign.Bank Division.ids (output total forward backward) t.val ∧
      PrivateVisit.Clean t ∧ PrivateZero.Clean t ∧ Blank t.val 839 ∧ Blank t.val 830 ∧
      (∀p,heap total backward ≤ p→
        p<heap total backward+(2^(total+1)-1)*stride (count total) (wordWidth total)→t.val.memory p=false) ∧
      Memory.Frame (heap total backward) ((2^(total+1)-1)*stride (count total) (wordWidth total)) s.val.memory t.val.memory ∧
      ArchiveFrame work s.val t.val ∧
      (∀i∈SourceArithmetic.sourcePorts,RationalAccumulator.Word t.val i (seed total forward backward i)) := by
  obtain ⟨c0,a,e0,h0,ba,za,f0⟩:=Prepare.executes (seed total forward backward) (bits total forward backward)
    (by dsimp only [bits];omega) (seed_words total forward backward) input tape s hb hz
  have a839:=RationalAccumulator.blank_of_eq (f0.tapes 839 (by decide)) h839
  have a830:=RationalAccumulator.blank_of_eq (f0.tapes 830 (by decide)) h830
  have aExtra : PrivateZero.Clean a := by
    intro i hi
    have disjoint : Disjoint PrivateZero.banks SourceArithmetic.work := by decide
    exact RationalAccumulator.blank_of_eq (f0.tapes i (Finset.disjoint_left.mp disjoint hi)) (he i hi)
  have baSmall : NatAssign.Bank Division.ids (Prepare.output (seed total forward backward)) a.val :=
    fun i hi => ba i (Finset.mem_union_left _ hi)
  have wa : ∀i∈Division.ids,(Prepare.output (seed total forward backward) i).bits.length ≤
      stageBits total forward backward := fun i hi =>
    Prepare.words _ _ (by dsimp only [bits];omega) (seed_words total forward backward) i (Finset.mem_union_left _ hi)
  have positive : 0<Prepare.output (seed total forward backward) 810 := by
    rw [Prepare.output_depth]
    change 0<wordWidth total
    dsimp only [wordWidth];omega
  obtain ⟨c1,b,e1,h1,bb,zb,b839,f1⟩:=Depth.executes _ (stageBits total forward backward) positive
    (Prepare.output_two _) (prepared_zero total forward backward) wa input tape a baSmall za a839
  have b830:=RationalAccumulator.blank_of_eq (f1.tapes 830 (by decide)) a830
  have bExtra:=PrivateZero.clean_of_binary aExtra f1 (Finset.Subset.refl _)
  have zero813 : selected total forward backward 813=0 := by
    rw [selected_other _ _ _ _ (by decide) (by decide),Prepare.output_other _ _ (by decide)]
    rfl
  obtain ⟨c2,c,e2,h2,bc,zc,c830,f2⟩:=Power.executes (selected total forward backward) zero813
    input tape b bb zb b830
  have c839:=RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide)) b839
  have cExtra : PrivateZero.Clean c := by
    intro i hi
    have disjoint : Disjoint PrivateZero.banks ({830,813} : Finset ℕ) := by decide
    exact RationalAccumulator.blank_of_eq (f2.tapes i (Finset.disjoint_left.mp disjoint hi)) (bExtra i hi)
  have two : powered total forward backward 819=2 := by
    rw [powered,Function.update_of_ne (by decide : (819 : ℕ)≠813),
      selected_other _ _ _ _ (by decide) (by decide),Prepare.output_two]
  have population : 0<powered total forward backward 813 := by
    simp only [powered,Function.update_self]
    positivity
  obtain ⟨c3,t,e3,h3,bt,zt,tExtra,t839,zeros,m3,f3⟩:=Allocation.executes (powered total forward backward)
    (stageBits total forward backward) population two (powered_words total forward backward)
    input tape c bc zc cExtra c839
  have t830:=RationalAccumulator.blank_of_eq (f3.tapes 830 (by omega) (by decide)) c830
  have before : c.val.memory=s.val.memory := f2.memory.trans (f1.memory.trans f0.memory)
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,zt,tExtra,t839,t830,?_,?_,
    ((ArchiveFrame.of_binary f0).mono (by decide)).trans
      (((ArchiveFrame.of_binary f1).mono (by decide)).trans
        (((ArchiveFrame.of_binary f2).mono (by decide)).trans (f3.mono (by decide)))),?_⟩
  · rw [selected_depth] at h2
    dsimp only [cost]
    omega
  · simpa only [powered_base,allocation_length] using zeros
  · simpa only [powered_base,allocation_length,before] using m3
  · intro i hi
    have hlo : 10 ≤ i := by simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi;omega
    have hdivision : i∉Division.work := by
      simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    have hpower : i∉({830,813} : Finset ℕ) := by
      simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    have halloc : i∉Allocation.work := by
      simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    have word:=ba i (Finset.mem_union_right _ hi)
    rw [Prepare.output_other _ _ (by
      simp only [SourceArithmetic.sourcePorts,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide)] at word
    exact RationalAccumulator.word_of_eq ((f3.tapes i (Or.inr hlo) halloc).trans
      ((f2.tapes i hpower).trans (f1.tapes i hdivision))) word

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
