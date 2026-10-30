import Maxwell.Continuum.SourceRoutingScatterRuntime

/-! A fixed countdown traverses every stored incidence exactly once. The
forward cursor and both written array prefixes are part of its invariant. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000

def loopWork : Finset ℕ := {779}∪work
def loopCode : Code := CountedShifted.code 779 stepCode
def loopCost {k n : ℕ} (p : Plan k n) (width : ℕ) : ℕ :=
  (k+1)*(13*width+15)+k*stepCost p

theorem counter_archive {s t : Store} (hf : CountedShifted.Frame 779 s t) :
    ArchiveFrame loopWork s.val t.val :=
  ⟨hf.2.1,hf.2.2.2.1,hf.2.2.2.2.1,fun j _ hj => hf.2.2.2.2.2.1 j (by
    intro he; subst j; exact hj (by simp [loopWork]))⟩

theorem loop_executes {k n : ℕ} (p : Plan k n)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hvalue : addressValue xs=k) (s : Store) (hs : Runtime p 0 s)
    (hcounter : s.val.tapes 779=BitTape.shifted xs origin) :
    ∃steps t finalWord, Executes input tape loopCode steps s t ∧ steps≤loopCost p xs.length ∧
      Runtime p k t ∧ t.val.tapes 779=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      RoutingOutside p.routing s.val t.val ∧ ArchiveFrame loopWork s.val t.val := by
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤k ∧ Runtime p (k-remaining) st ∧
    RoutingOutside p.routing s.val st.val ∧ ArchiveFrame loopWork s.val st.val
  have stable : ∀r a b, CountedShifted.Frame 779 a b→inv r a→inv r b := by
    intro r a b hf hh
    exact ⟨hh.1,hh.2.1.counted hf,hh.2.2.1.trans (RoutingOutside.of_memory hf.2.2.1),
      hh.2.2.2.trans (counter_archive hf)⟩
  have body : ∀r ys a, inv (r+1) a→a.val.tapes 779=BitTape.shifted ys origin→addressValue ys=r→
      ∃cost t, Executes input tape stepCode cost a t ∧ inv r t ∧
        t.val.tapes 779=BitTape.shifted ys origin ∧ cost≤stepCost p := by
    intro r ys a hh hword _
    let i : Fin k := ⟨k-(r+1),by have := hh.1; omega⟩
    obtain ⟨cost,t,he,hc,ht,ho,hf⟩ := runtime_step p i input tape a hh.2.1
    have hindex : i.val+1=k-r := by dsimp [i]; have := hh.1; omega
    rw [hindex] at ht
    exact ⟨cost,t,he,⟨by have := hh.1; omega,ht,hh.2.2.1.trans ho,
      hh.2.2.2.trans (hf.mono (Finset.subset_union_right))⟩,
      (hf.tapes 779 (by decide) (by decide)).trans hword,hc⟩
  have initial : inv k s := by
    exact ⟨le_rfl,by simpa using hs,RoutingOutside.refl _ _,ArchiveFrame.refl _ _⟩
  obtain ⟨steps,t,word,he,ht,hw,hl,_flag,hc⟩ := CountedShifted.executes 779 origin stepCode input tape
    inv (fun _ => stepCost p) stable body k xs s hvalue hcounter initial
  refine ⟨steps,t,word,he,?_,by simpa using ht.2.1,hw,hl,ht.2.2.1,ht.2.2.2⟩
  simpa only [loopCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

#print axioms loop_executes

end Maxwell.Cost.RoutingPorts.Complete.Scatter
