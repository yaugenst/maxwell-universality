import Maxwell.Cost.RealSparseOrder.Load
import Maxwell.Cost.RealSparseOrder.SourceIndexBounds
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealSparseOrder.Load
open RealSimulation RealSimulation.Control RealSimulation.IndexWidth
open RealSparse (execute execute_sound entryAt input)

/-- The loader starts at an existing store, preserving every untouched bank. -/
noncomputable def initializedFrom (s : RAMState) (m : ℕ) : RAMState :=
  let s := s.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 2
  let s := s.setIndex 3 m
  let s := s.setIndex 4 0
  let s := s.setIndex 5 1
  let s := s.setIndex 6 100
  s.setIndex 9 100

theorem initialize_steps_from (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc=0) :
    execute (program.next (input es vector) tape) 8 s = some (initializedFrom s es.length) := by
  simp [execute,program,Machine.next,RAMState.setIndex,initializedFrom,hpc]

theorem initializedFrom_ready (s : RAMState) (m : ℕ) (hpc : s.pc=0) :
    Ready (initializedFrom s m) m 0 := by
  simp [Ready,initializedFrom,RAMState.setIndex,hpc]

theorem initializedFrom_bound {B : ℕ} (s : RAMState) (m : ℕ)
    (hs : IndexBound B s) (hm : 100+m≤B) : IndexBound B (initializedFrom s m) := by
  unfold initializedFrom
  exact (((((((hs.setIndex 0 0 (by omega)).setIndex 1 1 (by omega)).setIndex 2 2 (by omega)).setIndex 3 m (by omega)).setIndex 4 0 (by omega)).setIndex 5 1 (by omega)).setIndex 6 100 (by omega)).setIndex 9 100 (by omega)

theorem advanced_bound {B m k : ℕ} (s : RAMState) (e : SparseEntry)
    (hs : IndexBound B s) (hr : Ready s m k) (hk : k<m)
    (hm : 100+4*m≤B) (he : e.row≤B ∧ e.column≤B) :
    IndexBound B (advanced s e) := by
  rcases hr with ⟨_,_,_,_,_,hi,ha,hc,hv⟩
  have hb : IndexBound B {s with pc:=9} := hs
  have hmid : IndexBound B (middle s e) := by
    unfold middle
    exact (((((hb.setIndex 7 e.row he.1).setIndex (s.indices 6) e.row he.1).setIndex 5 (s.indices 5+1) (by omega)).setIndex 7 e.column he.2).setIndex 8 (s.indices 6+1) (by omega)).setIndex (s.indices 6+1) e.column he.2
  have hw : IndexBound B (((middle s e).setWord 0 e.value).setWord (s.indices 9) e.value) := hmid
  exact (((hw.setIndex 5 (s.indices 5+2) (by omega)).setIndex 6 (s.indices 6+2) (by omega)).setIndex 9 (s.indices 9+1) (by omega)).setIndex 4 (s.indices 4+1) (by omega)

theorem literals {B : ℕ} (hb : 100≤B) : LiteralBound B program := by
  intro dst value h
  simp [program] at h
  rcases h with h|h|h|h|h|h|h <;> omega

private theorem inflate {B : ℕ} {s : RAMState} (hs : IndexBound B s) :
    IndexBound (2^30*B) s := hs.mono (by norm_num; omega)

/-- Each fourteen-instruction scan cycle restarts from the same cap. -/
theorem bounded_loop {B : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (hroom : 100+4*es.length≤B) (entries : ∀e∈es,e.row≤B ∧e.column≤B)
    (remaining k : ℕ) (s : RAMState) (hr : Ready s es.length k)
    (hc : k+remaining=es.length) (hs : IndexBound B s) :
    ∃ t, VisitedSteps (program.next (input es vector) tape) (IndexBound (2^30*B))
      (14*remaining+1) s t ∧ t.pc=22 ∧ IndexBound B t := by
  have hi := source_input_bound es vector (by omega) entries
  have hl := literals (by omega : 100≤B)
  induction remaining generalizing k s with
  | zero =>
    have hk : k=es.length := by omega
    subst k
    let t : RAMState := {s with pc:=22}
    have step : program.next (input es vector) tape s=some t := by
      simp [Machine.next,program,hr.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,t]
    have ht : IndexBound B t := hs
    exact ⟨t,.step (inflate hs) step (.refl (inflate ht)),rfl,ht⟩
  | succ remaining ih =>
    have hk : k<es.length := by omega
    have hb := advanced_bound s (entryAt es k) hs hr hk hroom (entryAt_bound entries k)
    obtain ⟨t,ht,hpc,hbound⟩ := ih (k+1) (advanced s (entryAt es k))
      (advanced_ready s _ k hr _) (by omega) hb
    have cycleTrace := visited_index_bound hs hl hi le_rfl
      (execute_sound _ (cycle es vector tape s k hr hk))
    have cycleTrace' : VisitedSteps (program.next (input es vector) tape)
        (IndexBound (2^30*B)) 14 s (advanced s (entryAt es k)) :=
      cycleTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
    refine ⟨t,?_,hpc,hbound⟩
    convert cycleTrace'.trans ht using 1
    omega

/-- The unchanged loader is a certified long call from any bounded store.
The trace includes every cycle and the compiler's actual return jump. -/
theorem bounded_executes_from {B : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (s : Store) (hs : IndexBound B s.val) (hroom : 100+4*es.length≤B)
    (entries : ∀e∈es,e.row≤B ∧e.column≤B) :
    ∃ t : Store, BoundedExecutes B 30 (input es vector) tape (.call program)
      (14*es.length+10) s t ∧ IndexBound B t.val := by
  have hinit := initializedFrom_bound s.val es.length hs (by omega)
  obtain ⟨t,ht,hpc,hbound⟩ := bounded_loop es vector tape hroom entries es.length 0
    (initializedFrom s.val es.length) (initializedFrom_ready s.val es.length s.property)
    (by omega) hinit
  have hi := source_input_bound es vector (by omega) entries
  have hl := literals (by omega : 100≤B)
  have initTrace := visited_index_bound hs hl hi le_rfl
    (execute_sound _ (initialize_steps_from es vector tape s.val s.property))
  have initTrace' : VisitedSteps (program.next (input es vector) tape)
      (IndexBound (2^30*B)) 8 s.val (initializedFrom s.val es.length) :=
    initTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
  have full : VisitedSteps (program.next (input es vector) tape)
      (IndexBound (2^30*B)) (14*es.length+9) s.val t := by
    convert initTrace'.trans ht using 1
    omega
  refine ⟨Store.ofState t,?_,hbound⟩
  have halt : program.code[t.pc]?=some .halt := by simp [program,hpc]
  convert BoundedExecutes.tracedCall full halt hs hbound using 1

end Maxwell.Cost.RealSparseOrder.Load
