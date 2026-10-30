import Maxwell.Continuum.SourceRoutingSortRuntime

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def loopWork : Finset ℕ := {1240}∪stepWork
def loopCode : Code := CountedShifted.code 1240 stepCode
def loopCost {q : ℕ} (p : Plan q) (round counterWidth : ℕ) : ℕ :=
  (q*q+1)*(13*counterWidth+15)+q*q*stepCost p round

theorem counter_archive {s t : Store} (frame : CountedShifted.Frame 1240 s t) :
    ArchiveFrame loopWork s.val t.val :=
  ⟨frame.2.1,frame.2.2.2.1,frame.2.2.2.2.1,fun j _ hj => frame.2.2.2.2.2.1 j (by
    intro h;subst j;exact hj (by simp [loopWork]))⟩

theorem loop_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (initial : Vector (List Bool) (q*q))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hvalue : addressValue xs=q*q) (s : Store) (state : Runtime p round saved initial 0 s)
    (counter : s.val.tapes 1240=BitTape.shifted xs origin) :
    ∃steps t finalWord,Executes input tape loopCode steps s t ∧ steps ≤ loopCost p round xs.length ∧
      Runtime p round saved initial (q*q) t ∧ t.val.tapes 1240=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ ArchiveFrame loopWork s.val t.val ∧
      Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining ≤ q*q ∧
    Runtime p round saved initial (q*q-remaining) st ∧ ArchiveFrame loopWork s.val st.val ∧
    Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory st.val.memory
  have stable : ∀r a b,CountedShifted.Frame 1240 a b→inv r a→inv r b := by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hh.2.2.1.trans (counter_archive hf),
      by simpa only [hf.2.2.1] using hh.2.2.2⟩
  have body : ∀r ys a,inv (r+1) a→a.val.tapes 1240=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t,Executes input tape stepCode cost a t ∧ inv r t ∧
        t.val.tapes 1240=BitTape.shifted ys origin ∧ cost ≤ stepCost p round := by
    intro r ys a hh hword _
    let i : Fin (q*q) := ⟨q*q-(r+1),by have := hh.1;omega⟩
    obtain ⟨cost,t,he,hc,ht,hf,hm⟩:=Runtime.step fit i input tape a hh.2.1
    have hindex : i.val+1=q*q-r := by dsimp only [i];have := hh.1;omega
    rw [hindex] at ht
    exact ⟨cost,t,he,⟨by have := hh.1;omega,ht,
      hh.2.2.1.trans (hf.mono Finset.subset_union_right),hh.2.2.2.trans hm⟩,
      (hf.tapes 1240 (by decide) (by decide)).trans hword,hc⟩
  have start : inv (q*q) s :=
    ⟨le_rfl,by simpa only [Nat.sub_self] using state,ArchiveFrame.refl _ _,Tree.Memory.Frame.refl _ _ _⟩
  obtain ⟨steps,t,word,he,ht,hw,hl,_,hc⟩:=CountedShifted.executes 1240 origin stepCode input tape
    inv (fun _ => stepCost p round) stable body (q*q) xs s hvalue counter start
  refine ⟨steps,t,word,he,?_,by simpa only [Nat.sub_zero] using ht.2.1,hw,hl,ht.2.2.1,ht.2.2.2⟩
  simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

theorem loopCost_polynomial {q : ℕ} (p : Plan q) (round : ℕ) :
    loopCost p round p.width ≤ 2^202*(q*q+1)*(p.bound round+3)^2 := by
  have width:=p.width_bound round
  have small : 13*p.width+15 ≤ 16*(p.bound round+3)^2 := by nlinarith
  have first:=Nat.mul_le_mul_left (q*q+1) small
  have second:=Nat.mul_le_mul_right (stepCost p round) (Nat.le_succ (q*q))
  dsimp only [loopCost,stepCost] at *
  nlinarith only [first,second]

#print axioms loop_executes
#print axioms loopCost_polynomial
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
