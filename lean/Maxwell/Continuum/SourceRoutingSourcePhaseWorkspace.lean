import Maxwell.Continuum.SourceRoutingSourcePhaseArrays
import Maxwell.Continuum.SourceRoutingPhaseStartupMachine

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePhase
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem tree_work_upper (i : ℕ) (hi : i∈SourceTree.work) : i<1200 := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact (SourcePlan.work_upper i hi).trans (by decide)
  · have upper : ∀j∈Tree.CompleteTree.work,j<1200 := by decide +kernel
    exact upper i hi

theorem tree_fresh {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Incidence.Result S p s) (hf : ArchiveFrame SourceTree.work s.val t.val)
    (i : ℕ) (hi : 1200≤ i) : Blank t.val i := by
  have original : Blank s.val i := ⟨0,hs.fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega))⟩
  exact RationalAccumulator.blank_of_eq (hf.tapes i (Or.inr (by omega))
    (fun hh=>by have bound:=tree_work_upper i hh;omega)) original

theorem tree_ready {s : Store} (clean : Tree.PrivateVisit.Clean s) : GeometryArray.Ready s.val := by
  have blank (i : ℕ) (hi : i∈Tree.Workspace.small) : Blank s.val i :=
    (Tree.Workspace.clean_iff s).mp clean i (Finset.mem_union_left _ hi)
  exact ⟨⟨blank 0 (by decide),blank 1 (by decide),blank 2 (by decide),blank 3 (by decide),
    blank 5 (by decide),blank 6 (by decide),blank 8 (by decide),blank 9 (by decide)⟩,
    blank 7 (by decide),blank 37 (by decide)⟩

theorem base_order (S : Source.SparseSystem) (p : ℕ) (slot : Fin 5) (hs : 2≤slot.val) :
    (plan S p).base 2≤(plan S p).base slot := by
  fin_cases slot <;> simp_all [plan,PhaseStartup.plan,PhaseStartup.bases]
  omega

theorem forward_before (S : Source.SparseSystem) (p : ℕ) :
    (SourcePlan.treeLayout S p).forward≤(plan S p).base 2 := by
  have ho:=ordered S p
  change (layout S p).forward≤(layout S p).backward+11*(side S p*side S p*(side S p*side S p).bits.length)+
    side S p*side S p*(side S p*side S p).bits.length
  omega

theorem backward_before (S : Source.SparseSystem) (p : ℕ) :
    (layout S p).backward+side S p*side S p*(plan S p).width≤(plan S p).base 2 := by
  change (layout S p).backward+side S p*side S p*(side S p*side S p).bits.length≤
    (layout S p).backward+11*(side S p*side S p*(side S p*side S p).bits.length)+
      side S p*side S p*(side S p*side S p).bits.length
  omega

#print axioms tree_fresh
#print axioms tree_ready
end Maxwell.Cost.RoutingPorts.Complete.SourcePhase
