import Maxwell.Continuum.SourceRoutingAssemblyLevelState
import Maxwell.Continuum.RuntimeCounterClear

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (CountedShifted.code 831 AssemblyStep.code) (.call (TapeOps.clear 831))
def cost {rows columns depth : ℕ} (p : Plan rows columns depth) : ℕ :=
  (2^depth+1)*(13*(2^depth).bits.length+15)+
    2^depth*bodyCost (columns+rows) (uniformWidth p.L)+6*(2^depth).bits.length+4

theorem executes {rows columns depth : ℕ} (p : Plan rows columns depth)
    (input : List Bool) (tape : ℕ→Bool) (start : BitRAMState) (s : Store)
    (hs : State p 0 start s) (hc : RationalAccumulator.Word s.val 831 (2^depth)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost p ∧
      State p (2^depth) start t ∧ Blank t.val 831 := by
  obtain ⟨origin,ho⟩:=hc
  let invariant (remaining : ℕ) (t : Store) : Prop :=
    remaining ≤ 2^depth ∧ State p (2^depth-remaining) start t
  have stable (n : ℕ) (a b : Store) (hf : CountedShifted.Frame 831 a b)
      (ha : invariant n a) : invariant n b := ⟨ha.1,ha.2.counter hf⟩
  have body (n : ℕ) (xs : List Bool) (a : Store) (ha : invariant (n+1) a)
      (hx : a.val.tapes 831=BitTape.shifted xs origin) (_hv : addressValue xs=n) :
      ∃steps b,Executes input tape AssemblyStep.code steps a b ∧ invariant n b ∧
        b.val.tapes 831=BitTape.shifted xs origin ∧ steps ≤ bodyCost (columns+rows) (uniformWidth p.L) := by
    have hi : 2^depth-(n+1)<2^depth := by have hh:=ha.1;omega
    obtain ⟨steps,b,he,hcost,hb,hcounter⟩:=State.step p (2^depth-(n+1)) hi input tape start a ha.2
    refine ⟨steps,b,he,⟨by have hh:=ha.1;omega,?_⟩,hcounter.trans hx,hcost⟩
    have heq : 2^depth-(n+1)+1=2^depth-n := by have hh:=ha.1;omega
    simpa only [heq] using hb
  obtain ⟨lc,a,finalWord,el,ha,hw,hlen,_,hcost⟩:=CountedShifted.executes 831 origin AssemblyStep.code
    input tape invariant (fun _ => bodyCost (columns+rows) (uniformWidth p.L)) stable body (2^depth) (2^depth).bits s
    (addressValue_bits _) ho ⟨le_rfl,by simpa only [Nat.sub_self] using hs⟩
  obtain ⟨t,ec,zt,ft⟩:=RuntimeCounter.clear_executes 831 input tape finalWord origin a hw
  refine ⟨lc+(6*finalWord.length+4),t,el.seq ec,?_,?_,zt⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hcost
    norm_cast at hcost
    rw [hlen]
    dsimp only [cost]
    omega
  · have ht:=ha.2.clear ft
    simpa only [Nat.sub_zero] using ht

def loadedCode : Code := .seq (.call (WordTransfer.clone 813 831)) code

theorem loaded_executes {rows columns depth : ℕ} (p : Plan rows columns depth)
    (hn : p.initial 813=2^depth) (input : List Bool) (tape : ℕ→Bool)
    (start : BitRAMState) (s : Store) (hs : State p 0 start s) (h831 : Blank s.val 831) :
    ∃steps t,Executes input tape loadedCode steps s t ∧
      steps ≤ cost p+15*(2^depth).bits.length+17 ∧ State p (2^depth) start t ∧ Blank t.val 831 := by
  have count : RationalAccumulator.Word s.val 813 (2^depth) := by
    simpa only [values,Function.iterate_zero,Function.id_def,hn] using hs.bank 813 (by decide)
  obtain ⟨origin,ho⟩:=count
  obtain ⟨co,hco⟩:=h831
  obtain ⟨a,ec,tt,tf⟩:=WordCall.clone 813 831 (by decide) input tape (2^depth).bits origin co s ho hco
  have cf : BinaryPrecision.Frame {831} s.val a.val := by
    refine ⟨tf.1,tf.2.1,tf.2.2.1,tf.2.2.2.1,tf.2.2.2.2.1,?_⟩
    intro i hi
    rw [tt,Function.update_of_ne (show i≠831 by simpa using hi)]
  have ha:=hs.clear cf
  have ca : RationalAccumulator.Word a.val 831 (2^depth) := ⟨co,by simp only [tt,Function.update_self]⟩
  obtain ⟨steps,t,he,hcost,ht,zt⟩:=executes p input tape start a ha ca
  refine ⟨(15*((2 : ℕ)^depth).bits.length+17)+steps,t,?_,by omega,ht,zt⟩
  simpa only [loadedCode] using ec.seq he

#print axioms executes
#print axioms loaded_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
