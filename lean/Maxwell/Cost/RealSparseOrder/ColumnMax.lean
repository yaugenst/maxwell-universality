import Maxwell.Cost.RealSparseOrder.ColumnMaxLoop
import Maxwell.Cost.RealSparseOrder.ColumnMaxInit

namespace Maxwell.Cost.RealSparseOrder.ColumnMax
open RealSimulation.Control RealSimulation.IndexWidth

def code : Code := .seq (.call initProgram) loopCode

theorem literal_bound (B : ℕ) : LiteralBound B code.compile := by
  have checked : code.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤0)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  exact (show value≤0 by simpa using hv).trans (Nat.zero_le B)

structure Result (b : Buffer) (es : List SparseEntry) (s t : RAMState) : Prop where
  maximum : t.indices 42=columnCount es
  remaining : t.indices 43=0
  cursor : t.indices 44=b.coordinates+2*es.length+1
  frame : ∀j,j<42 ∨46≤j→t.indices j=s.indices j
  words : t.words=s.words
  records : Records b t es
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  indexOutput : t.indexOutput=s.indexOutput

theorem records_of_frame {b : Buffer} {es : List SparseEntry} {s t : RAMState}
    (hb : b.Safe) (hr : Records b s es)
    (hf : ∀j,46≤j→t.indices j=s.indices j) (hw : t.words=s.words) : Records b t es := by
  induction es generalizing b with
  | nil => trivial
  | cons e es ih =>
    exact ⟨(hf b.coordinates (by have hh:=hb.2; omega)).trans hr.1,
      (hf (b.coordinates+1) (by have hh:=hb.2; omega)).trans hr.2.1,
      by rw [hw]; exact hr.2.2.1,ih (hb.shift 1) hr.2.2.2⟩

/-- Column dimension is computed by a finite memory scan, with every load,
comparison, loop test, and initialization instruction charged. -/
theorem bounded_scan (input : RAMInput) (tape : ℕ→Bool) (B : ℕ)
    (s : Store) (b : Buffer) (es : List SparseEntry)
    (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hn : s.val.indices 26=es.length) (hb : s.val.indices 27=b.coordinates)
    (hsafe : b.Safe) (hr : Records b s.val es) (hs : IndexBound B s.val)
    (hc : b.coordinates+2*es.length+1≤B) (hcols : ∀e∈es,e.column+1≤B) :
    ∃cost t,cost≤10*es.length+5 ∧BoundedExecutes B 9 input tape code cost s t ∧
      Result b es s.val t.val := by
  let mid := Store.ofState (initialized s.val)
  have hconfig : Config mid.val b es.length 0 :=
    (config_ofState _ _ _ _).mpr (init_config s.val b es.length h1 h2 hn hb)
  have hrecords : Records b mid.val es := by
    have hh := initialized_records hr hsafe
    rw [records_stored] at hh ⊢
    exact hh
  have hbound : IndexBound B mid.val := initialized_index_bound hs (by rw [hb]; omega)
  obtain ⟨cost,t,hcost,run,hfinal,hframe,hwords,hcursor,houtput,hindex⟩ :=
    bounded_loop input tape B mid b es 0 hconfig hsafe hrecords hbound hc hcols
  have hf : ∀j,j<42 ∨46≤j→t.val.indices j=s.val.indices j := by
    intro j hj
    exact (hframe j hj).trans (initialized_frame s.val j (by omega))
  have hw : t.val.words=s.val.words := hwords
  have hrfinal : Records b t.val es := records_of_frame hsafe hr
    (fun j hj=>hf j (Or.inr hj)) hw
  refine ⟨4+cost,t,by omega,
    BoundedExecutes.seq (BoundedExecutes.atom (init_executes input tape s h1) (by omega) hs hbound) run,?_⟩
  exact ⟨by simpa using hfinal.maximum,hfinal.remaining,hfinal.cursor,hf,hw,hrfinal,
    hcursor,houtput,hindex⟩

theorem run (input : RAMInput) (tape : ℕ→Bool) (B : ℕ)
    (s : Store) (b : Buffer) (es : List SparseEntry)
    (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hn : s.val.indices 26=es.length) (hb : s.val.indices 27=b.coordinates)
    (hsafe : b.Safe) (hr : Records b s.val es) (hs : IndexBound B s.val)
    (hc : b.coordinates+2*es.length+1≤B) (hcols : ∀e∈es,e.column+1≤B) :
    ∃(cost : ℕ) (t : Store),cost≤10*es.length+5 ∧
      (runCapped (code.compile.next input tape) (10*es.length+6) s.val).finished=
        some (t.place code.size) ∧
      (runCapped (code.compile.next input tape) (10*es.length+6) s.val).instructions=cost ∧
      Result b es s.val t.val := by
  obtain ⟨cost,t,hcost,execution,result⟩ := bounded_scan input tape B s b es
    h1 h2 hn hb hsafe hr hs hc hcols
  have run := execution.executes.compiled_run (10*es.length+6) (by omega)
  exact ⟨cost,t,hcost,run.1,run.2,result⟩

end Maxwell.Cost.RealSparseOrder.ColumnMax
