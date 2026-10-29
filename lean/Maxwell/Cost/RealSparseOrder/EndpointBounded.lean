import Maxwell.Cost.RealSparseOrder.EndpointFrom
import Maxwell.Cost.RealSparseOrder.SourceIndexBounds

namespace Maxwell.Cost.RealSparseOrder.Endpoint
open RealSimulation.Control RealSimulation.IndexWidth

theorem literal_bound {B : ℕ} (hB : 100≤B) : LiteralBound B code.compile := by
  have checked : code.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤100)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  exact (show value≤100 by simpa using hv).trans hB

/-- Original-input loading and sorting share one cap, even when this actual
code runs after previous preprocessing. -/
theorem bounded_from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 100+4*es.length≤B)
    (he : ∀e∈es,e.row≤B ∧e.column≤B) :
    ∃(cost : ℕ) (t : Store),cost≤bound es.length ∧
      BoundedExecutes B 30 (RealSparse.input es vector) tape code cost s t ∧
      Sort.Config t.val (resultBuffer es.length) (spareBuffer es.length)
        (2^es.length.size) es.length ∧
      Records (resultBuffer es.length) t.val (bottomUpSort es) ∧
      DataFrame initialBuffer (2*es.length) s.val t.val ∧Merge.Channels s.val t.val := by
  obtain ⟨loaded,loadRun,stored,_⟩ := Load.from_state es vector tape s
  obtain ⟨other,loadBound,_⟩ := Load.bounded_executes_from es vector tape s hs hm he
  obtain ⟨_,rfl⟩ := loadRun.deterministic loadBound.executes
  let start := Store.ofState (Initialize.initialized es.length loaded.val)
  have hi : Sort.Bounded B start.val initialBuffer (Initialize.secondaryBuffer es.length) 1
      (singletonRuns es) := by
    have h := Initialize.bounded es loaded.val stored loadBound.finish hm
    exact ⟨(Sort.invariant_ofState _ _ _ _ _).mpr h.invariant,h.indices,h.sourceEnd,h.targetEnd,h.size⟩
  obtain ⟨cost,t,run⟩ := Sort.bounded_loop (RealSparse.input es vector) tape B start
    initialBuffer (Initialize.secondaryBuffer es.length) es hi
  have full : BoundedExecutes B 30 (RealSparse.input es vector) tape code
      ((14*es.length+10)+(11+cost)) s t :=
    .seq loadBound (.seq (.atom (Initialize.executes es vector tape loaded) (by omega)
      loadBound.finish hi.indices) run)
  obtain ⟨actual,u,hcost,actualRun,cfg,records,frame,channels⟩ := from_state es vector tape s
  obtain ⟨rfl,rfl⟩ := full.executes.deterministic actualRun
  exact ⟨_,_,hcost,full,cfg,records,frame,channels⟩

/-- Complete machine resource theorem, including every visited state. -/
theorem resources_from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 100+4*es.length≤B)
    (he : ∀e∈es,e.row≤B ∧e.column≤B) :
    ∃(cost : ℕ) (t : Store),cost≤bound es.length ∧
      Executes (RealSparse.input es vector) tape code cost s t ∧
      Sort.Config t.val (resultBuffer es.length) (spareBuffer es.length)
        (2^es.length.size) es.length ∧
      Records (resultBuffer es.length) t.val (bottomUpSort es) ∧
      RealSimulation.VisitedSteps (code.compile.next (RealSparse.input es vector) tape)
        (RealSimulation.IndexWordWidth (30+B.size)) cost s.val (t.place code.size) ∧
      DataFrame initialBuffer (2*es.length) s.val t.val ∧Merge.Channels s.val t.val := by
  obtain ⟨cost,t,hcost,run,cfg,records,frame,channels⟩ := bounded_from_state es vector tape B s hs hm he
  exact ⟨cost,t,hcost,run.executes,cfg,records,run.word_width (literal_bound (by omega))
    (source_input_bound es vector (by omega) he),frame,channels⟩

end Maxwell.Cost.RealSparseOrder.Endpoint
