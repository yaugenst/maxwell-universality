import Maxwell.Continuum.SourceRoutingPathPhaseStep

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
open Structured Maxwell.Logical.Routing GeometryPath
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def loopWork : Finset ℕ := {1242}∪footerWork
def loopCode (transpose : Bool) : Code := CountedShifted.code 1242 (GeometryPath.stepCode transpose)
def loopCost {q : ℕ} (p : Plan q) (n counterWidth : ℕ) : ℕ :=
  (2*q+1)*(13*counterWidth+15)+2*q*(2^244*(p.bound n+3)^2)

theorem counter_archive {s t : Store} (frame : CountedShifted.Frame 1242 s t) :
    ArchiveFrame loopWork s.val t.val :=
  ⟨frame.2.1,frame.2.2.2.1,frame.2.2.2.2.1,fun j _ hj => frame.2.2.2.2.2.1 j (by
    intro h;subst j;exact hj (by simp [loopWork]))⟩

theorem loop_executes {q : ℕ} (p : Plan q) (initial : SortArrays.Keys q) (start : Port q)
    (level cursor n : ℕ) (transpose : Bool) (memory : ℕ→Bool)
    (fit : GeometrySort.Fits p.history.width initial) (height : level+2*q ≤ 6*q) (capacity : cursor+240*q ≤ n)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hvalue : addressValue xs=2*q)
    (s : Store) (state : Runtime p initial start level cursor transpose memory 0 s)
    (counter : s.val.tapes 1242=BitTape.shifted xs origin) :
    ∃steps t finalWord,Executes input tape (loopCode transpose) steps s t ∧ steps ≤ loopCost p n xs.length ∧
      Runtime p initial start level cursor transpose memory (2*q) t ∧ t.val.tapes 1242=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ ArchiveFrame loopWork s.val t.val ∧
      Tree.Memory.Frame p.base (n*p.width) s.val.memory t.val.memory := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining ≤ 2*q ∧
    Runtime p initial start level cursor transpose memory (2*q-remaining) st ∧
    ArchiveFrame loopWork s.val st.val ∧ Tree.Memory.Frame p.base (n*p.width) s.val.memory st.val.memory
  have stable : ∀r a b,CountedShifted.Frame 1242 a b→inv r a→inv r b := by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hh.2.2.1.trans (counter_archive hf),
      by simpa only [hf.2.2.1] using hh.2.2.2⟩
  have body : ∀r ys a,inv (r+1) a→a.val.tapes 1242=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t,Executes input tape (GeometryPath.stepCode transpose) cost a t ∧ inv r t ∧
        t.val.tapes 1242=BitTape.shifted ys origin ∧ cost ≤ 2^244*(p.bound n+3)^2 := by
    intro r ys a hh hword _
    let i : Fin (2*q) := ⟨2*q-(r+1),by have := hh.1;omega⟩
    obtain ⟨cost,t,he,hc,ht,hf,hm⟩:=Runtime.step n fit height capacity i input tape a hh.2.1
    have hindex : i.val+1=2*q-r := by dsimp only [i];have := hh.1;omega
    rw [hindex] at ht
    exact ⟨cost,t,he,⟨by have := hh.1;omega,ht,hh.2.2.1.trans (hf.mono Finset.subset_union_right),hh.2.2.2.trans hm⟩,
      (hf.tapes 1242 (by decide) (by decide)).trans hword,hc⟩
  have initialState : inv (2*q) s :=
    ⟨le_rfl,by simpa only [Nat.sub_self] using state,ArchiveFrame.refl _ _,Tree.Memory.Frame.refl _ _ _⟩
  obtain ⟨steps,t,word,he,ht,hw,hl,_,hc⟩:=CountedShifted.executes 1242 origin (GeometryPath.stepCode transpose) input tape
    inv (fun _ => 2^244*(p.bound n+3)^2) stable body (2*q) xs s hvalue counter initialState
  refine ⟨steps,t,word,he,?_,by simpa only [Nat.sub_zero] using ht.2.1,hw,hl,ht.2.2.1,ht.2.2.2⟩
  simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

#print axioms loop_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathPhase
