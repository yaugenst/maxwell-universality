import Maxwell.Continuum.SourceRoutingSortStep
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def partialKeys {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (initial : Vector (List Bool) (q*q)) (k : ℕ) (hk : k ≤ q*q) : Vector (List Bool) (q*q) :=
  GeometryScatter.run id (fun i => (SortArrays.step round saved).get i) p.width initial k hk

structure Runtime {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (initial : Vector (List Bool) (q*q)) (k : ℕ) (s : Store) : Prop where
  bound : k ≤ q*q
  bank : NatAssign.Bank GeometryArithmetic.ids (seed p round k) s.val
  ready : GeometryArray.Ready s.val
  privateBlank : Blank s.val 1249
  metadata : Metadata p s.val
  source : BitArray.Represents s.val.memory p.source p.width (IncidenceEncoding.words p.width saved)
  destination : BitArray.Represents s.val.memory p.destination p.width (partialKeys p round saved initial k bound)

theorem Runtime.step {q : ℕ} {p : Plan q} {round : ℕ} {saved : SortArrays.Keys q}
    {initial : Vector (List Bool) (q*q)} (fit : Fits p.width saved) (i : Fin (q*q))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : Runtime p round saved initial i.val s) :
    ∃steps t,Executes input tape stepCode steps s t ∧ steps ≤ stepCost p round ∧
      Runtime p round saved initial (i.val+1) t ∧ ArchiveFrame stepWork s.val t.val ∧
      Tree.Memory.Frame p.destination (q*q*p.width) s.val.memory t.val.memory := by
  obtain ⟨steps,t,he,hc,bt,zt,t1249,mt,st,dt,ft,mem⟩:=step_executes p round saved fit i
    (partialKeys p round saved initial i.val state.bound) input tape s
    state.bank state.ready state.privateBlank state.metadata state.source state.destination
  exact ⟨steps,t,he,hc,⟨i.isLt,bt,zt,t1249,mt,st,dt⟩,ft,mem⟩

theorem Runtime.counter_frame {q : ℕ} {p : Plan q} {round : ℕ} {saved : SortArrays.Keys q}
    {initial : Vector (List Bool) (q*q)} {k : ℕ} {s t : Store}
    (state : Runtime p round saved initial k s) (memory : t.val.memory=s.val.memory)
    (keep : ∀j,j≠1240→t.val.tapes j=s.val.tapes j) :
    Runtime p round saved initial k t := by
  have word (j : ℕ) (hj : j≠1240) (n : ℕ) (h : RationalAccumulator.Word s.val j n) :
      RationalAccumulator.Word t.val j n := RationalAccumulator.word_of_eq (keep j hj) h
  have blank (j : ℕ) (hj : j≠1240) (h : Blank s.val j) : Blank t.val j :=
    RationalAccumulator.blank_of_eq (keep j hj) h
  refine ⟨state.bound,?_,?_,blank 1249 (by decide) state.privateBlank,?_,?_,?_⟩
  · intro j hj
    apply word j _ _ (state.bank j hj)
    simp only [GeometryArithmetic.ids,GeometryArithmetic.controls,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  · rcases state.ready with ⟨⟨h0,h1,h2,h3,h5,h6,h8,h9⟩,h7,h37⟩
    exact ⟨⟨blank 0 (by decide) h0,blank 1 (by decide) h1,blank 2 (by decide) h2,
      blank 3 (by decide) h3,blank 5 (by decide) h5,blank 6 (by decide) h6,
      blank 8 (by decide) h8,blank 9 (by decide) h9⟩,
      blank 7 (by decide) h7,blank 37 (by decide) h37⟩
  · exact ⟨word 711 (by decide) _ state.metadata.width,
      BankArray.word_of_eq (keep 718 (by decide)) state.metadata.clock⟩
  · rw [memory];exact state.source
  · rw [memory];exact state.destination

theorem Runtime.counted {q : ℕ} {p : Plan q} {round : ℕ} {saved : SortArrays.Keys q}
    {initial : Vector (List Bool) (q*q)} {k : ℕ} {s t : Store}
    (state : Runtime p round saved initial k s) (frame : CountedShifted.Frame 1240 s t) :
    Runtime p round saved initial k t := state.counter_frame frame.2.2.1 frame.2.2.2.2.2.1

theorem Runtime.complete {q : ℕ} {p : Plan q} {round : ℕ} {saved : SortArrays.Keys q}
    {initial : Vector (List Bool) (q*q)} {s : Store} (state : Runtime p round saved initial (q*q) s) :
    BitArray.Represents s.val.memory p.destination p.width
      (IncidenceEncoding.words p.width (SortArrays.step round saved)) := by
  have complete:=GeometryScatter.run_complete id Function.injective_id
    (fun i => (SortArrays.step round saved).get i) p.width initial (SortArrays.step round saved) (fun _ => rfl)
  simpa only [partialKeys,complete] using state.destination

#print axioms Runtime.step
#print axioms Runtime.complete
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
