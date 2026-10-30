import Maxwell.Continuum.SourceRoutingLevelState
import Maxwell.Continuum.RuntimeCounterClear

/-! One fixed binary-countdown loop visits every node of a level. The
actual body theorem supplies execution, memory preservation and bit cost. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (CountedShifted.code 831 Step.code) (.call (TapeOps.clear 831))
def bodyCost (k B : ℕ) : ℕ := 2^300*(2*2^k+1)*(B+2)^3
def cost {k : ℕ} (p : Plan k) : ℕ :=
  (p.nodes+1)*(13*p.nodes.bits.length+15)+p.nodes*bodyCost k p.B+6*p.nodes.bits.length+4

theorem executes {k : ℕ} (p : Plan k) (input : List Bool) (tape : ℕ→Bool)
    (start : BitRAMState) (s : Store) (hs : State p 0 start s) (hc : RationalAccumulator.Word s.val 831 p.nodes) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ cost p ∧
      State p p.nodes start t ∧ Blank t.val 831 := by
  obtain ⟨origin,ho⟩ := hc
  let invariant (remaining : ℕ) (t : Store) : Prop :=
    remaining ≤ p.nodes ∧ State p (p.nodes-remaining) start t
  have stable (n : ℕ) (a b : Store) (hf : CountedShifted.Frame 831 a b)
      (ha : invariant n a) : invariant n b := ⟨ha.1,ha.2.counter hf⟩
  have body (n : ℕ) (xs : List Bool) (a : Store) (ha : invariant (n+1) a)
      (hx : a.val.tapes 831=BitTape.shifted xs origin) (_hv : addressValue xs=n) :
      ∃steps b,Executes input tape Step.code steps a b ∧ invariant n b ∧
        b.val.tapes 831=BitTape.shifted xs origin ∧ steps ≤ bodyCost k p.B := by
    have hi : p.nodes-(n+1)<p.nodes := by have hh:=ha.1;omega
    obtain ⟨steps,b,he,hcost,hb,hcounter⟩ := State.step p (p.nodes-(n+1)) hi input tape start a ha.2
    refine ⟨steps,b,he,⟨by have hh:=ha.1;omega,?_⟩,hcounter.trans hx,hcost⟩
    have heq : p.nodes-(n+1)+1=p.nodes-n := by have hh:=ha.1;omega
    simpa only [heq] using hb
  obtain ⟨lc,a,finalWord,el,ha,hw,hlen,_,hcost⟩ := CountedShifted.executes 831 origin Step.code
    input tape invariant (fun _ => bodyCost k p.B) stable body p.nodes p.nodes.bits s
    (addressValue_bits p.nodes) ho ⟨le_rfl,by simpa only [Nat.sub_self] using hs⟩
  obtain ⟨t,ec,zt,ft⟩ := RuntimeCounter.clear_executes 831 input tape finalWord origin a hw
  refine ⟨lc+(6*finalWord.length+4),t,el.seq ec,?_,?_,zt⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hcost
    norm_cast at hcost
    rw [hlen]
    dsimp only [cost]
    omega
  · have ht:=ha.2.clear ft
    simpa only [Nat.sub_zero] using ht

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
