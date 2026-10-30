import Maxwell.Continuum.SourceRoutingScatter

/-! The same fixed program scatters every real incidence and fills the
unoccupied ports to produce both complete permutation arrays. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Permutation
open Structured Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def code : Code := .seq Scatter.code cursorCode
def cost {k n : ℕ} (p : Scatter.Plan k n) : ℕ := Scatter.cost p+cursorCost p.routing
def work : Finset ℕ := Scatter.loopWork∪cursorWork

theorem executes {k n : ℕ} (p : Scatter.Plan k n)
    (hsource : Function.Injective p.source) (htarget : Function.Injective p.target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Scatter.Runtime p 0 s)
    (hcount : Word s.val 142 k) (h779 : Blank s.val 779) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost p ∧ Ready t.val ∧ Metadata p.routing t.val ∧
      Stored p.routing ((DummyFill.scatter (DummyFill.pairs p.source p.target)).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs p.source p.target).map Prod.swap)).map Fin.val) t.val ∧
      RoutingOutside p.routing s.val t.val ∧ ArchiveFrame work s.val t.val := by
  obtain ⟨ca,a,ea,hca,ra,sa,a730,a731,_a779,oa,fa⟩ := Scatter.partial_tables p hsource htarget
    input tape s hs hcount h779
  obtain ⟨cb,t,eb,hcb,rt,mt,st,ft⟩ := completion_executes p.routing p.source p.target hsource htarget
    input tape a ra.ready ra.metadata sa a730 a731
  exact ⟨ca+cb,t,ea.seq eb,Nat.add_le_add hca hcb,rt,mt,st,oa.trans ft.outside,
    (fa.mono (Finset.subset_union_left)).trans
      ((ArchiveFrame.of_complete ft.control).mono (Finset.subset_union_right))⟩

theorem compiled_run {k n : ℕ} (p : Scatter.Plan k n)
    (hsource : Function.Injective p.source) (htarget : Function.Injective p.target)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Scatter.Runtime p 0 s)
    (hcount : Word s.val 142 k) (h779 : Blank s.val 779) :
    ∃t : Store, (runPriced (code.compile.next input tape) (cost p+1) s.val).finished=some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (cost p+1) s.val).instructions≤cost p ∧
      Stored p.routing ((DummyFill.scatter (DummyFill.pairs p.source p.target)).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs p.source p.target).map Prod.swap)).map Fin.val) t.val := by
  obtain ⟨steps,t,he,hc,_rt,_mt,st,_ho,_hf⟩ := executes p hsource htarget input tape s hs hcount h779
  have hr := he.compiled_run (cost p+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hc,st⟩

#print axioms executes
#print axioms compiled_run

end Maxwell.Cost.RoutingPorts.Complete.Permutation
