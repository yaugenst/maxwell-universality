import Maxwell.Continuum.SourceRoutingAssemblyTraversalStep

/-! The fixed reverse traversal visits every internal routing level and
returns the exact root labels. Its counter, copies and cleanup are charged. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (CountedShifted.code 830 AssemblyLevel.nextCode) (.call (TapeOps.clear 830))
def cost (heap rows total : ℕ) : ℕ :=
  (total+1)*(13*total.bits.length+15)+total*bodyCost heap rows total+6*total.bits.length+4

theorem executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (input : List Bool) (tape : ℕ→Bool)
    (start : BitRAMState) (s : Store) (hs : State v heap rows total root 0 start s)
    (hc : RationalAccumulator.Word s.val 830 total) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost heap rows total ∧
      State v heap rows total root total start t ∧ Blank t.val 830 := by
  obtain ⟨origin,ho⟩:=hc
  let invariant (remaining : ℕ) (t : Store) : Prop :=
    remaining ≤ total ∧ State v heap rows total root (total-remaining) start t
  have stable (n : ℕ) (a b : Store) (hf : CountedShifted.Frame 830 a b)
      (ha : invariant n a) : invariant n b := ⟨ha.1,ha.2.counter_step hf⟩
  have body (n : ℕ) (xs : List Bool) (a : Store) (ha : invariant (n+1) a)
      (hx : a.val.tapes 830=BitTape.shifted xs origin) (_hv : addressValue xs=n) :
      ∃steps b,Executes input tape AssemblyLevel.nextCode steps a b ∧ invariant n b ∧
        b.val.tapes 830=BitTape.shifted xs origin ∧ steps ≤ bodyCost heap rows total := by
    have hi : total-(n+1)<total := by have hh:=ha.1;omega
    obtain ⟨steps,b,he,hcost,hb,hcounter⟩:=State.step v heap rows total root setup
      (total-(n+1)) hi input tape start a ha.2
    refine ⟨steps,b,he,⟨by have hh:=ha.1;omega,?_⟩,hcounter.trans hx,hcost⟩
    have heq : total-(n+1)+1=total-n := by have hh:=ha.1;omega
    simpa only [heq] using hb
  obtain ⟨lc,a,finalWord,el,ha,hw,hlen,_,hcost⟩:=CountedShifted.executes 830 origin AssemblyLevel.nextCode
    input tape invariant (fun _ => bodyCost heap rows total) stable body total total.bits s
    (addressValue_bits _) ho ⟨le_rfl,by simpa only [Nat.sub_self] using hs⟩
  obtain ⟨t,ec,zt,ft⟩:=RuntimeCounter.clear_executes 830 input tape finalWord origin a hw
  refine ⟨lc+(6*finalWord.length+4),t,el.seq ec,?_,?_,zt⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hcost
    norm_cast at hcost
    rw [hlen]
    dsimp only [cost]
    omega
  · have ht:=ha.2.clear ft
    simpa only [Nat.sub_zero] using ht

def loadedCode : Code := .seq (.call (WordTransfer.clone 810 830)) code

theorem loaded_executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (depth : v 810=total)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State v heap rows total root 0 start s) (h830 : Blank s.val 830) :
    ∃steps t,Executes input tape loadedCode steps s t ∧
      steps ≤ cost heap rows total+15*total.bits.length+17 ∧
      State v heap rows total root total start t ∧ Blank t.val 830 := by
  have count : RationalAccumulator.Word s.val 810 total := by
    simpa only [values,depth] using hs.bank 810 (by decide)
  obtain ⟨origin,ho⟩:=count
  obtain ⟨co,hco⟩:=h830
  obtain ⟨a,ec,tt,tf⟩:=WordCall.clone 810 830 (by decide) input tape total.bits origin co s ho hco
  have cf : BinaryPrecision.Frame {830} s.val a.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠830 by simpa using hi)]
  have ha:=hs.clear cf
  have ca : RationalAccumulator.Word a.val 830 total := ⟨co,by simp only [tt,Function.update_self]⟩
  obtain ⟨steps,t,he,hcost,ht,zt⟩:=executes v heap rows total root setup input tape start a ha ca
  exact ⟨(15*total.bits.length+17)+steps,t,ec.seq he,by omega,ht,zt⟩

#print axioms executes
#print axioms loaded_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyTraversal
