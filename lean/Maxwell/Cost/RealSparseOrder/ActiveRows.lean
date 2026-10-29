import Maxwell.Cost.RealSparseOrder.EndpointBounded
import Maxwell.Cost.RealSparseOrder.RelabelBounded
import Maxwell.Cost.RealSparseOrder.RelabelControlFrame

namespace Maxwell.Cost.RealSparseOrder.ActiveRows
open RealSimulation.Control RealSimulation.IndexWidth

def code : Code := .seq Endpoint.code Relabel.code

def bound (m : ℕ) : ℕ := Endpoint.bound m+21*m+12

def entries (es : List SparseEntry) : List SparseEntry := Relabel.relabeled none 0 (bottomUpSort es)
def retained (es : List SparseEntry) : List ℕ := Relabel.retained none (bottomUpSort es)

/-- The already computed transpose product lies above both sorting buffers
and the original-row/RHS map; all these high cells remain unchanged. -/
def Frame (m : ℕ) (s t : RAMState) : Prop :=
  (∀j,100+5*m≤j → t.indices j=s.indices j) ∧
  (∀j,100+5*m≤j → t.words j=s.words j)

structure Result (es : List SparseEntry) (vector : ℕ→ℝ) (s t : RAMState) : Prop where
  records : Records (Endpoint.resultBuffer es.length) t (entries es)
  gathered : Relabel.Gathered (Relabel.outputBase es.length) (Relabel.outputBase es.length)
    t vector (retained es)
  rankCount : t.indices 35=(retained es).length
  originalCount : t.indices 26=es.length
  frame : Frame es.length s t
  channels : Merge.Channels s t
  zero : t.indices 0=0
  one : t.indices 1=1
  two : t.indices 2=2
  coordinateBase : t.indices 27=(Endpoint.resultBuffer es.length).coordinates
  coefficientBase : t.indices 28=(Endpoint.resultBuffer es.length).coefficients

/-- One finite program reads, orders, relabels and gathers from the original
input while preserving earlier high-buffer computations. -/
theorem bounded_from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 100+5*es.length≤B)
    (he : ∀e∈es,es.length+e.row≤B ∧e.column+1≤B) :
    ∃cost t,cost≤bound es.length ∧
      BoundedExecutes B 30 (RealSparse.input es vector) tape code cost s t ∧
      Result es vector s.val t.val := by
  have labels : ∀e∈es,e.row≤B ∧e.column≤B := by
    intro e he'
    obtain ⟨hr,hc⟩ := he e he'
    constructor <;> omega
  obtain ⟨first,mid,hfirst,sortRun,cfg,records,sortFrame,sortChannels⟩ :=
    Endpoint.bounded_from_state es vector tape B s hs (by omega) labels
  have hlen : (bottomUpSort es).length=es.length := bottomUpSort_length es
  have ends := Endpoint.result_end es.length
  have hmap : (Endpoint.resultBuffer es.length).coordinates+2*(bottomUpSort es).length≤
      Relabel.outputBase (bottomUpSort es).length := by
    rw [hlen]
    exact ends.1
  have hrhs : (Endpoint.resultBuffer es.length).coefficients+(bottomUpSort es).length≤
      Relabel.outputBase (bottomUpSort es).length := by
    rw [hlen]
    unfold Relabel.outputBase
    omega
  have boundRows : ∀e∈bottomUpSort es,(bottomUpSort es).length+e.row≤B := by
    intro e he'
    rw [hlen]
    exact (he e ((bottomUpSort_perm es).mem_iff.mp he')).1
  obtain ⟨rest,t,hrest,relabelRun,result⟩ := Relabel.bounded_scan es (bottomUpSort es) vector tape B mid
    (Endpoint.resultBuffer es.length) hlen cfg.zero cfg.one cfg.two (by rw [hlen]; exact cfg.count)
    cfg.sourceRow (Endpoint.result_safe _) hmap hrhs records sortRun.finish
    (by rw [hlen]; omega) (by rw [hlen]; unfold Relabel.outputBase; omega) boundRows
  have controls := Relabel.scan_preserves_controls (RealSparse.input es vector) tape mid t
    (Endpoint.resultBuffer es.length) (bottomUpSort es) rest cfg.zero cfg.one cfg.two
    (by rw [hlen]; exact cfg.count) cfg.sourceRow (Endpoint.result_safe _) hmap hrhs records relabelRun.executes
  refine ⟨first+rest,t,?_,.seq sortRun (relabelRun.mono le_rfl (by omega)),?_⟩
  · unfold bound
    rw [hlen] at hrest
    omega
  · refine ⟨result.records,?_,result.config.count,?_,?_,?_,result.config.zero,result.config.one,result.config.two,?_,?_⟩
    · simpa only [hlen,retained] using result.gathered
    · simpa only [hlen] using result.config.originalCount
    · constructor
      · intro j hj
        have hr := result.frame.1 j (by omega)
          (Or.inr (by rw [hlen]; omega))
          (Or.inr (by rw [hlen]; unfold Relabel.outputBase; omega))
        exact hr.trans (sortFrame.1 j (by omega) (Or.inr (by simp only [initialBuffer]; omega)))
      · intro j hj
        have hr := result.frame.2 j (by omega)
          (Or.inr (by rw [hlen]; unfold Relabel.outputBase; omega))
        exact hr.trans (sortFrame.2 j (by omega) (Or.inr (by simp only [initialBuffer]; omega)))
    · exact ⟨result.randomCursor.trans sortChannels.1,result.output.trans sortChannels.2.1,
        result.indexOutput.trans sortChannels.2.2⟩
    · exact (controls 27 (Or.inl (by omega))).trans cfg.sourceRow
    · exact (controls 28 (Or.inl (by omega))).trans cfg.sourceValue

theorem literal_bound {B : ℕ} (hB : 100≤B) : LiteralBound B code.compile := by
  have checked : code.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤100)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  exact (show value≤100 by simpa using hv).trans hB

theorem Result.rank_le {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) : t.indices 35≤es.length := by
  rw [h.rankCount]
  exact (Relabel.retained_length_le none (bottomUpSort es)).trans_eq (bottomUpSort_length es)

theorem Result.preserved_transpose {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) (j : ℕ) :
    t.words (100+6*es.length+j)=s.words (100+6*es.length+j) := h.frame.2 _ (by omega)

/-- The capped interpreter, semantic arrays and all intermediate word sizes
refer to this one literal composed machine. -/
theorem run (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (hs : IndexBound B s.val) (hm : 100+5*es.length≤B)
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

end Maxwell.Cost.RealSparseOrder.ActiveRows
