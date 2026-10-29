import Maxwell.Cost.RealSparseOrder.RelabelLoop
import Maxwell.Cost.RealSparseOrder.RelabelInit
import Maxwell.Cost.RealSparseOrder.RelabelMeaning

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

def code : Code := .seq (.call initProgram) loopCode

structure Result (b : Buffer) (es : List SparseEntry) (vector : ℕ→ℝ) (s t : RAMState) : Prop where
  config : Config t (b.shift es.length) 0 (lastRow none es) (retained none es).length
    es.length (outputBase es.length) (outputBase es.length)
  records : Records b t (relabeled none 0 es)
  gathered : Gathered (outputBase es.length) (outputBase es.length) t vector (retained none es)
  frame : Frame b es.length (outputBase es.length) (outputBase es.length) 0 s t
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  indexOutput : t.indexOutput=s.indexOutput

/-- The actual original sparse input tape supplies every gathered RHS
coordinate; neither rank discovery nor gathering uses a host lookup. -/
theorem scan_executes (original es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (s : Store) (b : Buffer) (hlen : es.length=original.length)
    (h0 : s.val.indices 0=0) (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hm : s.val.indices 26=es.length) (hc : s.val.indices 27=b.coordinates)
    (hb : b.Safe) (hmap : b.coordinates+2*es.length≤outputBase es.length)
    (hrhs : b.coefficients+es.length≤outputBase es.length) (hs : Records b s.val es) :
    ∃cost t,cost≤21*es.length+12 ∧
      Executes (RealSparse.input original vector) tape code cost s t ∧Result b es vector s.val t.val := by
  let mid := Store.ofState (initialized s.val)
  have hconfig : Config mid.val b es.length none 0 es.length
      (outputBase es.length) (outputBase es.length) :=
    (config_ofState _ _ _ _ _ _ _ _).mpr (init_config s.val b es.length h0 h1 h2 hm hc)
  have hrecords : Records b mid.val es := by
    have hh := initialized_records hs hb
    rw [records_stored] at hh ⊢
    exact hh
  obtain ⟨cost,t,hcost,run,hfinal,hr,hg,hf,hcursor,houtput,hindex⟩ :=
    executes (RealSparse.input original vector) tape vector mid b es none 0 es.length
      (outputBase es.length) (outputBase es.length) hconfig hb hmap hrhs hrecords
      (fun row=>by rw [hlen]; exact RealSparse.input_vector original vector row)
  have hframe : Frame b es.length (outputBase es.length) (outputBase es.length) 0 s.val mid.val := by
    constructor
    · intro j hj _ _
      exact initialized_indices_frame s.val j (Or.inr (by omega))
    · intro _ _ _; rfl
  refine ⟨11+cost,t,by omega,Executes.seq (init_executes _ tape s) run,?_⟩
  exact ⟨by simpa using hfinal,hr,by simpa using hg,hframe.trans hf,hcursor,houtput,hindex⟩

theorem Result.rank_bound {b : Buffer} {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result b es vector s t) : t.indices 35≤es.length := by
  rw [h.config.count]
  exact retained_length_le none es

theorem Result.row_bound {b : Buffer} {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result b es vector s t) :
    ∀e∈relabeled none 0 es,e.row<t.indices 35 := by
  rw [h.config.count]
  simpa using relabeled_row_lt none 0 es (by simp)

/-- A finite compiled machine, with a fixed linear cap, implements the
whole initializer and scan and returns the exact retained-label/RHS arrays. -/
theorem run (original es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (s : Store) (b : Buffer) (hlen : es.length=original.length)
    (h0 : s.val.indices 0=0) (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hm : s.val.indices 26=es.length) (hc : s.val.indices 27=b.coordinates)
    (hb : b.Safe) (hmap : b.coordinates+2*es.length≤outputBase es.length)
    (hrhs : b.coefficients+es.length≤outputBase es.length) (hs : Records b s.val es) :
    ∃(cost : ℕ) (t : Store),cost≤21*es.length+12 ∧
      (runCapped (code.compile.next (RealSparse.input original vector) tape)
        (21*es.length+13) s.val).finished=some (t.place code.size) ∧
      (runCapped (code.compile.next (RealSparse.input original vector) tape)
        (21*es.length+13) s.val).instructions=cost ∧Result b es vector s.val t.val := by
  obtain ⟨cost,t,hcost,hcode,hresult⟩ :=
    scan_executes original es vector tape s b hlen h0 h1 h2 hm hc hb hmap hrhs hs
  have hr := hcode.compiled_run (21*es.length+13) (by omega)
  exact ⟨cost,t,hcost,hr.1,hr.2,hresult⟩

end Maxwell.Cost.RealSparseOrder.Relabel
