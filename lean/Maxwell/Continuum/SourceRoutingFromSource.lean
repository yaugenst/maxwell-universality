import Maxwell.Continuum.SourceRoutingSourceInitialize

/-! Source-produced endpoint arrays feed one fixed permutation program.
The theorem includes startup, allocation, every incidence, and completion
of unused ports; none of those arrays are supplied by an oracle. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Structured SourceGraph.Positive Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def code : Code := .seq prepareCode Permutation.code
def cost (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  prepareCost S p+Permutation.cost (plan S p [] room)
def work : Finset ℕ := prepareWork∪Permutation.work

theorem executes (S : Source.SparseSystem) (p : ℕ) (hm : 2≤S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost S p hs.room ∧ Ready t.val ∧
      Metadata (Startup.gridLayout (vertices S p) (base S p)) t.val ∧
      Stored (Startup.gridLayout (vertices S p) (base S p))
        ((DummyFill.scatter (DummyFill.pairs (source S p) (target S p))).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs (source S p) (target S p)).map Prod.swap)).map Fin.val) t.val ∧
      RoutingOutside (Startup.gridLayout (vertices S p) (base S p)) s.val t.val ∧
      ArchiveFrame work s.val t.val := by
  obtain ⟨ca,a,clock,ea,hca,ra,a142,a779,oa,fa⟩ := initializes S p hm input tape s hs
  obtain ⟨cb,t,eb,hcb,rt,mt,st,ot,ft⟩ := Permutation.executes (plan S p clock hs.room)
    (source_injective S p) (target_injective S p) input tape a ra a142 a779
  have hc : cb≤Permutation.cost (plan S p [] hs.room) := hcb
  exact ⟨ca+cb,t,ea.seq eb,Nat.add_le_add hca hc,rt,mt,st,oa.trans ot,
    (fa.mono Finset.subset_union_left).trans (ft.mono Finset.subset_union_right)⟩

theorem retained {S : Source.SparseSystem} {p : ℕ} {s t : Store}
    (hs : SourceGraph.Retain.Data S p s.val) (hf : ArchiveFrame work s.val t.val) :
    SourceGraph.Retain.Data S p t.val := by
  have keep (i : ℕ) (hi : 500 ≤ i) (hj : i≤509) : t.val.tapes i=s.val.tapes i := by
    apply hf.tapes i (Or.inr (by omega))
    simp only [work,prepareWork,Startup.allWork,Startup.banks,Size.banks,Initialize.work,
      Permutation.work,Scatter.loopWork,Scatter.work,PortArithmetic.privateWork,
      PortArithmetic.ids,PortArithmetic.ports,
      Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,cursorWork,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  exact ⟨hs.numeric.transport (fun i hi hj _ _ => keep i hi hj),
    RationalAccumulator.word_of_eq (keep 503 (by decide) (by decide)) hs.circuitSize,
    (keep 508 (by decide) (by decide)).trans hs.rhs⟩

#print axioms executes
#print axioms retained

end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
