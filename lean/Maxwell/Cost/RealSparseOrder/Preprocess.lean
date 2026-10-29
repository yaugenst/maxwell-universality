import Maxwell.Cost.RealSparseOrder.ActiveRows
import Maxwell.Cost.RealSparseOrder.ColumnMax

namespace Maxwell.Cost.RealSparseOrder.Preprocess
open RealSimulation.Control RealSimulation.IndexWidth

def code : Code := .seq ActiveRows.code ColumnMax.code

def bound (m : ℕ) : ℕ := ActiveRows.bound m+10*m+5

structure Result (es : List SparseEntry) (vector : ℕ→ℝ) (s t : RAMState) : Prop where
  active : ActiveRows.Result es vector s t
  columns : t.indices 42=ColumnMax.columnCount (ActiveRows.entries es)

private theorem columns_bound {B : ℕ} (es : List SparseEntry)
    (h : ∀e∈es,e.column+1≤B) : ∀e∈ActiveRows.entries es,e.column+1≤B := by
  intro e he
  have hm : (e.column,e.value)∈(bottomUpSort es).map (fun f=>(f.column,f.value)) := by
    rw [←Relabel.relabeled_columns_values none 0 (bottomUpSort es)]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  obtain ⟨f,hf,heq⟩ := List.mem_map.mp hm
  have hcol : f.column=e.column := congrArg Prod.fst heq
  rw [←hcol]
  exact h f ((bottomUpSort_perm es).mem_iff.mp hf)

private theorem gathered_after {map rhs : ℕ} {s t : RAMState} {vector : ℕ→ℝ} {rows : List ℕ}
    (h : Relabel.Gathered map rhs s vector rows) (hmap : 46≤map)
    (hi : ∀j,46≤j → t.indices j=s.indices j) (hw : t.words=s.words) :
    Relabel.Gathered map rhs t vector rows := by
  induction rows generalizing map rhs with
  | nil => trivial
  | cons row rows ih =>
    exact ⟨(hi map hmap).trans h.1,by rw [hw]; exact h.2.1,ih h.2.2 (by omega)⟩

theorem bounded_from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 101+5*es.length≤B)
    (he : ∀e∈es,es.length+e.row≤B ∧e.column+1≤B) :
    ∃cost t,cost≤bound es.length ∧
      BoundedExecutes B 30 (RealSparse.input es vector) tape code cost s t ∧
      Result es vector s.val t.val := by
  obtain ⟨first,mid,hfirst,firstRun,active⟩ := ActiveRows.bounded_from_state es vector tape B s hs (by omega) he
  have hlen : (ActiveRows.entries es).length=es.length := by
    simp only [ActiveRows.entries,Relabel.relabeled_length,bottomUpSort_length]
  have ends := Endpoint.result_end es.length
  obtain ⟨rest,t,hrest,lastRun,lastResult⟩ := ColumnMax.bounded_scan (RealSparse.input es vector) tape B mid
    (Endpoint.resultBuffer es.length) (ActiveRows.entries es) active.one active.two
    (by rw [hlen]; exact active.originalCount) active.coordinateBase (Endpoint.result_safe _) active.records
    firstRun.finish (by rw [hlen]; omega) (columns_bound es (fun e he'=>(he e he').2))
  refine ⟨first+rest,t,?_,.seq firstRun (lastRun.mono le_rfl (by omega)),?_⟩
  · unfold bound
    rw [hlen] at hrest
    omega
  · refine ⟨?_,lastResult.maximum⟩
    refine ⟨lastResult.records,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact gathered_after active.gathered (by unfold Relabel.outputBase; omega)
        (fun j hj=>lastResult.frame j (Or.inr hj)) lastResult.words
    · exact (lastResult.frame 35 (Or.inl (by omega))).trans active.rankCount
    · exact (lastResult.frame 26 (Or.inl (by omega))).trans active.originalCount
    · constructor
      · intro j hj
        exact (lastResult.frame j (Or.inr (by omega))).trans (active.frame.1 j hj)
      · intro j hj
        rw [lastResult.words]
        exact active.frame.2 j hj
    · exact ⟨lastResult.randomCursor.trans active.channels.1,lastResult.output.trans active.channels.2.1,
        lastResult.indexOutput.trans active.channels.2.2⟩
    · exact (lastResult.frame 0 (Or.inl (by omega))).trans active.zero
    · exact (lastResult.frame 1 (Or.inl (by omega))).trans active.one
    · exact (lastResult.frame 2 (Or.inl (by omega))).trans active.two
    · exact (lastResult.frame 27 (Or.inl (by omega))).trans active.coordinateBase
    · exact (lastResult.frame 28 (Or.inl (by omega))).trans active.coefficientBase

set_option maxRecDepth 5000 in
theorem literal_bound {B : ℕ} (hB : 100≤B) : LiteralBound B code.compile := by
  have checked : code.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤100)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  exact (show value≤100 by simpa using hv).trans hB

/-- The actual input-preserving sparse preprocessing program has one total
cost and one uniform intermediate-word bound. -/
theorem run (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 101+5*es.length≤B)
    (he : ∀e∈es,es.length+e.row≤B ∧e.column+1≤B) :
    ∃(cost : ℕ) (t : Store),cost≤bound es.length ∧
      (runCapped (code.compile.next (RealSparse.input es vector) tape)
        (bound es.length+1) s.val).finished=some (t.place code.size) ∧
      (runCapped (code.compile.next (RealSparse.input es vector) tape)
        (bound es.length+1) s.val).instructions=cost ∧
      Result es vector s.val t.val ∧
      RealSimulation.VisitedSteps (code.compile.next (RealSparse.input es vector) tape)
        (RealSimulation.IndexWordWidth (30+B.size)) cost s.val (t.place code.size) := by
  obtain ⟨cost,t,hcost,execution,result⟩ := bounded_from_state es vector tape B s hs hm he
  have actual := execution.executes.compiled_run (bound es.length+1) (by omega)
  have inputBound : InputBound B (RealSparse.input es vector) :=
    source_input_bound es vector (by omega) (by
      intro e he'
      obtain ⟨hr,hc⟩ := he e he'
      constructor <;> omega)
  exact ⟨cost,t,hcost,actual.1,actual.2,result,
    execution.word_width (literal_bound (by omega)) inputBound⟩

end Maxwell.Cost.RealSparseOrder.Preprocess
