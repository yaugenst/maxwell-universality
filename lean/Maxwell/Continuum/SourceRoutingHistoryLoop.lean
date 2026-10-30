import Maxwell.Continuum.SourceRoutingHistoryRuntime

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def loopWork : Finset ℕ := {1241}∪stepWork
def loopCode : Code := CountedShifted.code 1241 stepCode
def loopCost {q : ℕ} (p : Plan q) (counterWidth : ℕ) : ℕ :=
  (2*q+1)*(13*counterWidth+15)+2*q*stepCost p

theorem counter_archive {s t : Store} (frame : CountedShifted.Frame 1241 s t) :
    ArchiveFrame loopWork s.val t.val :=
  ⟨frame.2.1,frame.2.2.2.1,frame.2.2.2.2.1,fun j _ hj => frame.2.2.2.2.2.1 j (by
    intro h;subst j;exact hj (by simp [loopWork]))⟩

theorem loop_executes {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q)
    (fit : GeometrySort.Fits p.width initial) (input : List Bool) (tape : ℕ→Bool)
    (xs : List Bool) (origin : ℤ) (hvalue : addressValue xs=2*q) (s : Store)
    (state : Runtime p initial 0 s) (counter : s.val.tapes 1241=BitTape.shifted xs origin) :
    ∃steps t finalWord,Executes input tape loopCode steps s t ∧ steps ≤ loopCost p xs.length ∧
      Runtime p initial (2*q) t ∧ t.val.tapes 1241=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ ArchiveFrame loopWork s.val t.val ∧
      MemoryFrame p s.val.memory t.val.memory := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining ≤ 2*q ∧
    Runtime p initial (2*q-remaining) st ∧ ArchiveFrame loopWork s.val st.val ∧
    MemoryFrame p s.val.memory st.val.memory
  have stable : ∀r a b,CountedShifted.Frame 1241 a b→inv r a→inv r b := by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hh.2.2.1.trans (counter_archive hf),
      by simpa only [hf.2.2.1] using hh.2.2.2⟩
  have body : ∀r ys a,inv (r+1) a→a.val.tapes 1241=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t,Executes input tape stepCode cost a t ∧ inv r t ∧
        t.val.tapes 1241=BitTape.shifted ys origin ∧ cost ≤ stepCost p := by
    intro r ys a hh hword _
    let i : Fin (2*q) := ⟨2*q-(r+1),by have := hh.1;omega⟩
    obtain ⟨cost,t,he,hc,ht,hf,hm⟩:=Runtime.step fit i input tape a hh.2.1
    have hindex : i.val+1=2*q-r := by dsimp only [i];have := hh.1;omega
    rw [hindex] at ht
    exact ⟨cost,t,he,⟨by have := hh.1;omega,ht,
      hh.2.2.1.trans (hf.mono Finset.subset_union_right),hh.2.2.2.trans hm⟩,
      (hf.tapes 1241 (by decide) (by decide)).trans hword,hc⟩
  have start : inv (2*q) s :=
    ⟨le_rfl,by simpa only [Nat.sub_self] using state,ArchiveFrame.refl _ _,Tree.Memory.Frame.refl _ _ _⟩
  obtain ⟨steps,t,word,he,ht,hw,hl,_,hc⟩:=CountedShifted.executes 1241 origin stepCode input tape
    inv (fun _ => stepCost p) stable body (2*q) xs s hvalue counter start
  refine ⟨steps,t,word,he,?_,by simpa only [Nat.sub_zero] using ht.2.1,hw,hl,ht.2.2.1,ht.2.2.2⟩
  simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

theorem loopCost_polynomial {q : ℕ} (p : Plan q) :
    loopCost p (2*q).bits.length ≤ 2^208*(q+1)^3*(p.bound+3)^2 := by
  have counterWidth:=Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ (2*q))
  change (2*q).bits.length ≤ (2*q+1).bits.length at counterWidth
  have width : (2*q).bits.length ≤ p.bound := by dsimp only [Plan.bound];omega
  have small : 13*(2*q).bits.length+15 ≤ 16*(p.bound+3)^2 := by nlinarith
  have first:=Nat.mul_le_mul_left (2*q+1) small
  have volume : 2*q*(q*q+1) ≤ 2*(q+1)^3 := by nlinarith
  have linear : 2*q+1 ≤ 2*(q+1)^3 := by nlinarith
  have firstBound:=Nat.mul_le_mul_right (16*(p.bound+3)^2) linear
  have mainBound:=Nat.mul_le_mul_right (2^206*(p.bound+3)^2) volume
  dsimp only [loopCost,stepCost]
  nlinarith only [first,firstBound,mainBound]

#print axioms loop_executes
#print axioms loopCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
