import Maxwell.Continuum.SourceRoutingTraversalStep

/-! A single fixed outer countdown program executes all non-root split
levels.  Its state invariant contains the concrete stored tree outputs. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq (CountedShifted.code 830 Level.nextCode) (.call (TapeOps.clear 830))
def cost (heap rows total : ℕ) : ℕ :=
  total*(13*(total-1).bits.length+15)+(total-1)*bodyCost heap rows total+6*(total-1).bits.length+4

theorem executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Setup v heap rows total) (input : List Bool) (tape : ℕ→Bool)
    (start : BitRAMState) (s : Store) (hs : State v heap rows total root 0 start s)
    (hc : RationalAccumulator.Word s.val 830 (total-1)) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost heap rows total ∧
      State v heap rows total root (total-1) start t ∧ Blank t.val 830 := by
  obtain ⟨origin,ho⟩:=hc
  let invariant (remaining : ℕ) (t : Store) : Prop :=
    remaining ≤ total-1 ∧ State v heap rows total root (total-1-remaining) start t
  have stable (n : ℕ) (a b : Store) (hf : CountedShifted.Frame 830 a b)
      (ha : invariant n a) : invariant n b := ⟨ha.1,ha.2.counter_step hf⟩
  have body (n : ℕ) (xs : List Bool) (a : Store) (ha : invariant (n+1) a)
      (hx : a.val.tapes 830=BitTape.shifted xs origin) (_hv : addressValue xs=n) :
      ∃steps b,Executes input tape Level.nextCode steps a b ∧ invariant n b ∧
        b.val.tapes 830=BitTape.shifted xs origin ∧ steps ≤ bodyCost heap rows total := by
    have hi : total-1-(n+1)<total-1 := by have hh:=ha.1;omega
    obtain ⟨steps,b,he,hcost,hb,hcounter⟩:=State.step v heap rows total root setup
      (total-1-(n+1)) hi input tape start a ha.2
    refine ⟨steps,b,he,⟨by have hh:=ha.1;omega,?_⟩,hcounter.trans hx,hcost⟩
    have heq : total-1-(n+1)+1=total-1-n := by have hh:=ha.1;omega
    simpa only [heq] using hb
  obtain ⟨lc,a,finalWord,el,ha,hw,hlen,_,hcost⟩:=CountedShifted.executes 830 origin Level.nextCode
    input tape invariant (fun _ => bodyCost heap rows total) stable body (total-1) (total-1).bits s
    (addressValue_bits _) ho ⟨le_rfl,by simpa only [Nat.sub_self] using hs⟩
  obtain ⟨t,ec,zt,ft⟩:=RuntimeCounter.clear_executes 830 input tape finalWord origin a hw
  refine ⟨lc+(6*finalWord.length+4),t,el.seq ec,?_,?_,zt⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hcost
    norm_cast at hcost
    rw [hlen]
    have hp:=setup.positive
    dsimp only [cost]
    have hc : total-1+1=total := by omega
    rw [hc] at hcost
    omega
  · have ht:=ha.2.clear ft
    simpa only [Nat.sub_zero] using ht

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Traversal
