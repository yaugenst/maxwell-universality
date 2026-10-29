import Maxwell.Cost.ChildPermutation.LoopSupport
import Maxwell.Cost.ChildPermutation.Step

namespace Maxwell.Cost.ChildPermutation
open Structured
open RationalAccumulator (Blank)
open scoped BigOperators

private theorem fill_congr {k : ℕ} (width : ℕ) (d : Data k) (out : Outputs k)
    {a b : ℕ} (h : a=b) (ha : a ≤ 2^k) (hb : b ≤ 2^k) :
    fillOutputs width d out a ha = fillOutputs width d out b hb := by
  subst b
  rfl

def loopBody : Code := .seq stepCode (BankArray.incrementCode 81)
def loopCode : Code := .seq (CountedShifted.code 126 loopBody) (.call (TapeOps.clear 126))

def loopCost (layout : Layout) (k : ℕ) : ℕ :=
  (2^k+1)*(13*(2^k).bits.length+15) + 2^k*(550000*(budget layout (2^k).bits+1)^2) +
    6*(2^k).bits.length+4

/-- The fixed countdown traverses every source pair, builds both children
and their inverse tables, and clears its counter. -/
theorem loop_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (d : Data k) (out : Outputs k) (index clock childClock : List Bool)
    (hw : layout.parentWidth=k+2) (hc : clock.length=layout.parentWidth)
    (hcc : childClock.length=layout.childWidth) (hs : layout.Separated k)
    (hindex : addressValue index=0) (hlen : index.length ≤ (2^k).bits.length)
    (countOrigin : ℤ) (s : Store) (hcount : s.val.tapes 126=BitTape.shifted (2^k).bits countOrigin)
    (cfg : Config layout index clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory d out) :
    ∃ cost t finalIndex, cost ≤ loopCost layout k ∧ Executes input tape loopCode cost s t ∧
      addressValue finalIndex=2^k ∧ finalIndex.length ≤ (2^k).bits.length ∧
      Config layout finalIndex clock childClock t.val ∧ Workspace t.val ∧ Blank t.val 126 ∧
      Represents layout t.val.memory d (finalOutputs layout.childWidth d) ∧
      LoopFrame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  let n := 2^k
  let invariant := LoopInvariant layout d out clock childClock s.val
  let bound := 550000*(budget layout n.bits+1)^2
  have hcw : layout.childWidth=k+1 := by simp [Layout.childWidth,hw]
  have hnlen : n.bits.length=layout.childWidth := by
    rw [hcw]
    exact (by rw [Nat.size_eq_bits_len,Nat.size_pow] : (2^k).bits.length=k+1)
  have hnPower : n < 2^n.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
  have bodyCorrect : ∀ r xs u, invariant (r+1) u →
      u.val.tapes 126=BitTape.shifted xs countOrigin → addressValue xs=r →
      ∃ bodyCost t, Executes input tape loopBody bodyCost u t ∧ invariant r t ∧
        t.val.tapes 126=BitTape.shifted xs countOrigin ∧ bodyCost ≤ bound := by
    intro r xs u hu hcounter _
    obtain ⟨hr,idx,hidx,hlen',hcfg,hwork,hrep,hframe,hmemory⟩ := hu
    have hlt : n-(r+1) < n := by dsimp [n]; omega
    let j : Fin (2^k) := ⟨n-(r+1),hlt⟩
    obtain ⟨scost,a,hscost,es,acfg,awork,_,arep,aframe,amemory⟩ :=
      step_executes k input tape layout d
        (fillOutputs layout.childWidth d out (n-(r+1)) (Nat.sub_le _ _)) idx clock childClock j
        hw hidx (by rw [← hnlen]; exact hlen') hc hcc hs u hcfg hwork hrep
    obtain ⟨icost,t,hicost,ei,hti,_,htm,_,htapes,htf⟩ := BankArray.increment_bank 81 (by omega)
      input tape idx a acfg.index awork.1.1
    have hnew : addressValue (Increment.bits idx)=n-r := by rw [Increment.bits_value,hidx]; dsimp [n]; omega
    have hnewlen : (Increment.bits idx).length ≤ n.bits.length :=
      BankArray.increment_length_bound idx n.bits.length hlen' (by dsimp [n] at *; omega)
    have hprefix : n-r=(n-(r+1))+1 := by dsimp [n]; omega
    have hrepresented : Represents layout t.val.memory d
        (fillOutputs layout.childWidth d out (n-r) (Nat.sub_le _ _)) := by
      rw [htm]
      have heq : fillOutputs layout.childWidth d out (n-r) (Nat.sub_le _ _) =
          stepOutputs layout.childWidth d j
            (fillOutputs layout.childWidth d out (n-(r+1)) (Nat.sub_le _ _)) := by
        exact fill_congr layout.childWidth d out hprefix _ (by dsimp [n] at *; omega)
      rw [heq]
      exact arep
    refine ⟨scost+icost,t,es.seq ei,?_,?_,?_⟩
    · exact ⟨by dsimp [n] at *; omega,Increment.bits idx,hnew,hnewlen,
        config_update (fun i hi _ => htapes i hi) acfg hti,
        workspace_update (fun i hi _ => htapes i hi) awork,hrepresented,
        hframe.trans ((LoopFrame.of_step aframe).trans (LoopFrame.of_increment htf)),
        by simpa only [htm] using hmemory.trans amemory⟩
    · exact (htapes 126 (by omega)).trans
        ((aframe.2.2.2.1 126 (by omega) (by simp [Private,DoublingInit.Private,DoublingPass.Private])).trans hcounter)
    · have hb : budget layout idx ≤ budget layout n.bits := by dsimp [budget,n]; omega
      have hsc : scost ≤ 500000*(budget layout n.bits+1)^2 := hscost.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have hl : n.bits.length+20 ≤ budget layout n.bits := by dsimp [budget]; omega
      dsimp [bound]
      nlinarith
  have hinit : invariant n s := by
    dsimp only [invariant,LoopInvariant,n]
    refine ⟨le_rfl,index,?_,hlen,cfg,work,?_,LoopFrame.refl _,MemoryFrame.refl _ _ _⟩
    · simpa only [Nat.sub_self] using hindex
    · rw [fill_congr layout.childWidth d out (Nat.sub_self (2^k)) _ (Nat.zero_le _)]
      exact rep
  obtain ⟨lcost,l,finalCount,el,hinv,hltape,hlength,_,hlcost⟩ :=
    CountedShifted.executes 126 countOrigin loopBody input tape invariant (fun _ => bound)
      (invariant_stable layout d out clock childClock s.val) bodyCorrect n n.bits s
      (RationalAccumulator.address_bits n) hcount hinit
  obtain ⟨_,finalIndex,hval,hfinlen,cfgL,workL,repL,frameL,memoryL⟩ := hinv
  obtain ⟨t,et,htapes,tf⟩ := WordCall.clear 126 input tape finalCount countOrigin l hltape
  have keep (i : ℕ) (hi : i ≠ 126) : t.val.tapes i=l.val.tapes i := tf.2.2.2.2.2.1 i hi hi
  have tframe : LoopFrame l.val t.val :=
    ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,fun i _ _ hi _ => keep i hi,
      fun i _ hr => tf.2.2.2.2.2.2 i (by omega) (by omega)⟩
  refine ⟨_,t,finalIndex,?_,el.seq et,by simpa only [Nat.sub_zero] using hval,hfinlen,
    config_update (fun i _ hi => keep i hi) cfgL
      (BankArray.word_of_eq (keep 81 (by omega)) cfgL.index),
    workspace_update (fun i _ hi => keep i hi) workL,
    ⟨countOrigin+finalCount.length,by simp [htapes]⟩,?_,frameL.trans tframe,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlcost
    dsimp [loopCost]
    dsimp [bound,n] at hlcost hlength
    omega
  · simpa only [tf.2.2.1,Nat.sub_zero,fill_output] using repL
  · simpa only [tf.2.2.1] using memoryL

end Maxwell.Cost.ChildPermutation
