import Maxwell.Cost.RealSparseOrder.Relabel
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

set_option maxHeartbeats 800000 in
theorem processed_controls {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hb : 100≤b.coordinates) (hm : 100≤map) (hr : s.val.indices b.coordinates=row)
    (j : ℕ) (hj : j<32 ∨42≤j ∧j<100) :
    (processed input previous row s).val.indices j=s.val.indices j := by
  have hd : ∀i:ℕ,i<42→i≠map+count := by omega
  have hjc : j≠b.coordinates := by omega
  have hjm : j≠map+count := by omega
  have hjs : ∀ i : ℕ, 32 ≤ i → i < 42 → j ≠ i := by omega
  by_cases he : previous=some row
  · simp [processed,chosen,he,loaded,rewritten,Store.ofState,RAMState.setIndex,
      h.count,h.cursor,hjc,hjs]
  · simp [processed,chosen,he,loaded,created,rewritten,Store.ofState,RAMState.setIndex,
      RAMState.setWord,h.count,h.cursor,h.mapBase,h.rhsBase,hr,hd,hjc,hjm,hjs]

private theorem loop_controls_exists (input : RAMInput) (tape : ℕ→Bool)
    (s : Store) (b : Buffer) (es : List SparseEntry) (previous : Option ℕ)
    (count m map rhs : ℕ)
    (h : Config s.val b es.length previous count m map rhs)
    (hb : b.Safe) (hm : b.coordinates+2*es.length≤map)
    (hv : b.coefficients+es.length≤rhs) (hr : Records b s.val es) :
    ∃cost t,Executes input tape loopCode cost s t ∧
      ∀j,j<32 ∨42≤j ∧j<100→t.val.indices j=s.val.indices j := by
  induction es generalizing s b previous count with
  | nil =>
    exact ⟨1,s,Executes.done (by rw [h.one,h.remaining]; simp),fun _ _=>rfl⟩
  | cons e es ih =>
    have hmap : 100≤map := by have hh:=hb.2; simp only [List.length_cons] at hm; omega
    have hrhs : 100≤rhs := by have hh:=hb.1; simp only [List.length_cons] at hv; omega
    let mid := processed input previous e.row s
    let c := nextCount previous count e.row
    have hc : Config mid.val (b.shift 1) es.length (some e.row) c m map rhs := by
      simpa only [List.length_cons,Nat.add_sub_cancel] using processed_config h hb.2 hmap hr.1
    obtain ⟨first,_,firstRun⟩ := step input tape s b (e::es).length previous count m map rhs
      e.row h hb.2 hmap hrhs hr.1
    obtain ⟨rest,t,tailRun,hframe⟩ := ih mid (b.shift 1) (some e.row) c hc (hb.shift 1)
      (by simp only [Buffer.shift,List.length_cons] at *; omega)
      (by simp only [Buffer.shift,List.length_cons] at *; omega)
      (processed_records h hb hm hv hr (input:=input)).2.2.2
    refine ⟨1+first+rest,t,Executes.more (by rw [h.one,h.remaining]; simp) firstRun tailRun,?_⟩
    intro j hj
    exact (hframe j hj).trans (processed_controls h hb.2 hmap hr.1 j hj)

/-- Relabeling leaves the final sort descriptors and every other unused
control register unchanged. This applies to the same actual execution. -/
theorem scan_preserves_controls (input : RAMInput) (tape : ℕ→Bool)
    (s t : Store) (b : Buffer) (es : List SparseEntry) (cost : ℕ)
    (h0 : s.val.indices 0=0) (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hm : s.val.indices 26=es.length) (hc : s.val.indices 27=b.coordinates)
    (hb : b.Safe) (hmap : b.coordinates+2*es.length≤outputBase es.length)
    (hrhs : b.coefficients+es.length≤outputBase es.length) (hr : Records b s.val es)
    (execution : Executes input tape code cost s t) :
    ∀j,j<32 ∨42≤j ∧j<100→t.val.indices j=s.val.indices j := by
  let mid := Store.ofState (initialized s.val)
  have hconfig : Config mid.val b es.length none 0 es.length
      (outputBase es.length) (outputBase es.length) :=
    (config_ofState _ _ _ _ _ _ _ _).mpr (init_config s.val b es.length h0 h1 h2 hm hc)
  have hrecords : Records b mid.val es := by
    have hh := initialized_records hr hb
    rw [records_stored] at hh ⊢
    exact hh
  obtain ⟨rest,u,tailRun,hframe⟩ := loop_controls_exists input tape mid b es none 0 es.length
    (outputBase es.length) (outputBase es.length) hconfig hb hmap hrhs hrecords
  have actual : Executes input tape code (11+rest) s u :=
    Executes.seq (init_executes input tape s) tailRun
  have heq := (execution.deterministic actual).2
  subst u
  intro j hj
  exact (hframe j hj).trans (initialized_indices_frame s.val j (by omega))

end Maxwell.Cost.RealSparseOrder.Relabel
