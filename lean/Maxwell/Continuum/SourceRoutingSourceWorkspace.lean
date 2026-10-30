import Maxwell.Continuum.SourceRoutingPermutationWorkspace
import Maxwell.Continuum.SourceRoutingSourceArithmetic
import Maxwell.Continuum.SourceRoutingPrivateZero

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem work_upper (i : ℕ) (hi : i∈work) : i<800 := by
  simp only [work,prepareWork,Startup.allWork,Startup.banks,Size.banks,Initialize.work,
    Permutation.work,Scatter.loopWork,Scatter.work,PortArithmetic.privateWork,PortArithmetic.ids,
    PortArithmetic.ports,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,cursorWork,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem fresh_after {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val)
    (i : ℕ) (hi : 800 ≤ i) : Blank t.val i := by
  have original : Blank s.val i := ⟨0,hs.fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega))⟩
  exact RationalAccumulator.blank_of_eq
    (hf.tapes i (Or.inr (by omega)) (fun hh => by have bound:=work_upper i hh;omega)) original

theorem private_ready {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (ht : Ready t.val)
    (hf : ArchiveFrame work s.val t.val) : Tree.PrivateVisit.Clean t := by
  apply (Tree.Workspace.clean_iff t).mpr
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · rcases ht.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    simp only [Tree.Workspace.small,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h5
    · exact h6
    · exact ht.seven
    · exact h8
    · exact h9
    · exact ht.pack
  · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
    have bounds : 80 ≤ j ∧ j ≤ 196 := by
      simp only [Tree.NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false] at hj
      omega
    apply fresh_after hs hf
    rw [Tree.PrivateNode.shift_source j bounds]
    omega

theorem zero_ready {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val) : Tree.PrivateZero.Clean t := by
  intro i hi
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
  have bounds : 80 ≤ j ∧ j ≤ 196 := by
    simp only [Tree.ZeroHeap.banks,Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  apply fresh_after hs hf
  rw [Tree.PrivateNode.shift_source j bounds]
  omega

theorem division_fresh {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame work s.val t.val)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i) :
    ∀i∈Tree.Division.ids,Blank t.val i := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact fresh_after hs hf i ((Finset.mem_Icc.mp hi).1)
  · exact hz i hi

#print axioms private_ready
#print axioms division_fresh
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
