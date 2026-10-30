import Maxwell.Continuum.SourceRoutingFromSource

namespace Maxwell.Cost.RoutingPorts.Complete.Permutation
open Structured Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem executes_workspace {k n : ℕ} (p : Scatter.Plan k n)
    (hsource : Function.Injective p.source) (htarget : Function.Injective p.target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Scatter.Runtime p 0 s)
    (hcount : Word s.val 142 k) (h779 : Blank s.val 779) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost p ∧ Ready t.val ∧ Metadata p.routing t.val ∧
      Stored p.routing ((DummyFill.scatter (DummyFill.pairs p.source p.target)).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs p.source p.target).map Prod.swap)).map Fin.val) t.val ∧
      RoutingOutside p.routing s.val t.val ∧ ArchiveFrame work s.val t.val ∧
      (∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i) := by
  obtain ⟨ca,a,ea,hca,ra,sa,a730,a731,_a779,oa,fa⟩:=Scatter.partial_tables p hsource htarget
    input tape s hs hcount h779
  obtain ⟨cb,t,eb,hcb,rt,mt,st,ft⟩:=completion_executes p.routing p.source p.target hsource htarget
    input tape a ra.ready ra.metadata sa a730 a731
  refine ⟨ca+cb,t,ea.seq eb,Nat.add_le_add hca hcb,rt,mt,st,oa.trans ft.outside,
    (fa.mono Finset.subset_union_left).trans
      ((ArchiveFrame.of_complete ft.control).mono Finset.subset_union_right),?_⟩
  intro i hi
  have original : Blank a.val i := by
    have word:=ra.bank i (Finset.mem_union_left _ hi)
    rw [Scatter.seed_zero p.half k 0 0 i hi] at word
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp word
  apply RationalAccumulator.blank_of_eq (ft.control.tapes i ?_ ?_) original
  · simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hi;omega
  · simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> decide

#print axioms executes_workspace
end Maxwell.Cost.RoutingPorts.Complete.Permutation

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Structured SourceGraph.Positive Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem executes_workspace (S : Source.SparseSystem) (p : ℕ) (hm : 2 ≤ S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost S p hs.room ∧ Ready t.val ∧
      Metadata (Startup.gridLayout (vertices S p) (base S p)) t.val ∧
      Stored (Startup.gridLayout (vertices S p) (base S p))
        ((DummyFill.scatter (DummyFill.pairs (source S p) (target S p))).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs (source S p) (target S p)).map Prod.swap)).map Fin.val) t.val ∧
      RoutingOutside (Startup.gridLayout (vertices S p) (base S p)) s.val t.val ∧
      ArchiveFrame work s.val t.val ∧
      (∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,RationalAccumulator.Blank t.val i) := by
  obtain ⟨ca,a,clock,ea,hca,ra,a142,a779,oa,fa⟩:=initializes S p hm input tape s hs
  obtain ⟨cb,t,eb,hcb,rt,mt,st,ot,ft,zt⟩:=Permutation.executes_workspace (plan S p clock hs.room)
    (source_injective S p) (target_injective S p) input tape a ra a142 a779
  have hc : cb ≤ Permutation.cost (plan S p [] hs.room) := hcb
  exact ⟨ca+cb,t,ea.seq eb,Nat.add_le_add hca hc,rt,mt,st,oa.trans ot,
    (fa.mono Finset.subset_union_left).trans (ft.mono Finset.subset_union_right),zt⟩

#print axioms executes_workspace
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
