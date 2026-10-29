import Maxwell.Cost.RealTransposePreserve.Correctness
import Maxwell.Cost.RealSparseOrder.SourceIndexBounds
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealTransposePreserve
open RealSimulation RealSimulation.Control RealSimulation.IndexWidth
open RealSparse (execute execute_sound entryAt input)

set_option maxRecDepth 20000

private theorem inflate {B : ℕ} {s : RAMState} (hs : IndexBound B s) :
    IndexBound (2^30*B) s := hs.mono (by norm_num; omega)

/-- Product initialization changes only its six actual index destinations. -/
noncomputable def productInitializedFrom (s : RAMState) (m : ℕ) : RAMState :=
  (((((s.setIndex 0 0).setIndex 1 1).setIndex 2 m).setIndex 3 0).setIndex 4 1).setIndex 10 16

theorem product_initialize_steps (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (s : RAMState) (hpc : s.pc=0) :
    execute (RealSparse.program.next (input es vector) tape) 6 s =
      some (productInitializedFrom s es.length) := by
  simp [execute,RealSparse.program,Machine.next,RAMState.setIndex,productInitializedFrom,hpc]

theorem product_initialized_ready (s : RAMState) (m : ℕ) (hpc : s.pc=0) :
    RealSparse.Ready (productInitializedFrom s m) m 0 := by
  simp [RealSparse.Ready,productInitializedFrom,RAMState.setIndex,hpc]

theorem product_initialized_bound {B : ℕ} (s : RAMState) (m : ℕ)
    (hs : IndexBound B s) (hm : 16+m≤B) :
    IndexBound B (productInitializedFrom s m) := by
  unfold productInitializedFrom
  exact (((((hs.setIndex 0 0 (by omega)).setIndex 1 1 (by omega)).setIndex 2 m
    (by omega)).setIndex 3 0 (by omega)).setIndex 4 1 (by omega)).setIndex 10 16 (by omega)

theorem product_advanced_bound {B m k : ℕ} (s : RAMState) (e : SparseEntry) (x : ℝ)
    (hs : IndexBound B s) (hr : RealSparse.Ready s m k) (hk : k<m)
    (hm : 16+2*m≤B) (he : m+e.row≤B ∧16+e.column≤B) :
    IndexBound B (RealSparse.advanced s e x) := by
  rcases hr with ⟨_,_,_,hc,hi,ha,_⟩
  have hs0 : IndexBound B {s with pc:=7} := hs
  have hs1 := hs0.setIndex 5 e.row (by omega)
  have hs2 := hs1.setIndex 4 (s.indices 4+1) (by omega)
  have hs3 := hs2.setIndex 6 e.column (by omega)
  have hs4 := hs3.setIndex 7 (s.indices 2+e.row) (by omega)
  have hs5 := hs4.setIndex 8 (16+e.column) he.2
  have hs6 := hs5.setIndex 3 (s.indices 3+1) (by omega)
  exact hs6.setIndex 4 (s.indices 4+2) (by omega)

theorem product_literals {B : ℕ} (hB : 16≤B) : LiteralBound B RealSparse.program := by
  intro dst value h
  simp [RealSparse.program] at h
  rcases h with h|h|h|h|h <;> omega

/-- Each fifteen-step product cycle returns to the original index cap. -/
theorem product_bounded_loop {B label : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (hroom : 100+8*es.length+label≤B)
    (entries : ∀e∈es,e.row≤label ∧e.column≤label)
    (remaining k : ℕ) (s : RAMState) (hr : RealSparse.Ready s es.length k)
    (hc : k+remaining=es.length) (hs : IndexBound B s) :
    ∃ t, VisitedSteps (RealSparse.program.next (input es vector) tape)
      (IndexBound (2^30*B)) (15*remaining+1) s t ∧t.pc=21 ∧IndexBound B t := by
  have entriesB : ∀e∈es,e.row≤B ∧e.column≤B := by
    intro e he
    have h := entries e he
    constructor <;> omega
  have hi := RealSparseOrder.source_input_bound es vector (by omega : es.length≤B) entriesB
  have hl := product_literals (by omega : 16≤B)
  induction remaining generalizing k s with
  | zero =>
    have hk : k=es.length := by omega
    subst k
    let t : RAMState := {s with pc:=21}
    have step : RealSparse.program.next (input es vector) tape s=some t := by
      rcases hr with ⟨hpc,_,_,hm,hk,_,_⟩
      simp [Machine.next,RealSparse.program,hpc,hm,hk,t]
    have ht : IndexBound B t := hs
    exact ⟨t,.step (inflate hs) step (.refl (inflate ht)),rfl,ht⟩
  | succ remaining ih =>
    have hk : k<es.length := by omega
    have he := RealSparseOrder.entryAt_bound entries k
    have hb := product_advanced_bound s (entryAt es k) (vector (entryAt es k).row)
      hs hr hk (by omega) (by constructor <;> omega)
    obtain ⟨t,ht,hpc,hbound⟩ := ih (k+1)
      (RealSparse.advanced s (entryAt es k) (vector (entryAt es k).row))
      (RealSparse.advanced_ready s _ k hr _ _) (by omega) hb
    have cycleTrace := visited_index_bound hs hl hi le_rfl
      (execute_sound _ (RealSparse.cycle es vector tape s k hr hk))
    have cycleTrace' : VisitedSteps (RealSparse.program.next (input es vector) tape)
        (IndexBound (2^30*B)) 15 s
        (RealSparse.advanced s (entryAt es k) (vector (entryAt es k).row)) :=
      cycleTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
    refine ⟨t,?_,hpc,hbound⟩
    convert cycleTrace'.trans ht using 1
    omega

theorem product_bounded_from {B label : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (s : Store) (hs : IndexBound B s.val)
    (hroom : 100+8*es.length+label≤B)
    (entries : ∀e∈es,e.row≤label ∧e.column≤label) :
    ∃ t : Store, BoundedExecutes B 30 (input es vector) tape (.call RealSparse.program)
      (15*es.length+8) s t := by
  have hinit := product_initialized_bound s.val es.length hs (by omega)
  obtain ⟨t,ht,hpc,hbound⟩ := product_bounded_loop es vector tape hroom entries
    es.length 0 (productInitializedFrom s.val es.length)
    (product_initialized_ready s.val es.length s.property) (by omega) hinit
  have entriesB : ∀e∈es,e.row≤B ∧e.column≤B := by
    intro e he
    have h := entries e he
    constructor <;> omega
  have hi := RealSparseOrder.source_input_bound es vector (by omega : es.length≤B) entriesB
  have hl := product_literals (by omega : 16≤B)
  have initTrace := visited_index_bound hs hl hi le_rfl
    (execute_sound _ (product_initialize_steps es vector tape s.val s.property))
  have initTrace' : VisitedSteps (RealSparse.program.next (input es vector) tape)
      (IndexBound (2^30*B)) 6 s.val (productInitializedFrom s.val es.length) :=
    initTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
  have full : VisitedSteps (RealSparse.program.next (input es vector) tape)
      (IndexBound (2^30*B)) (15*es.length+7) s.val t := by
    convert initTrace'.trans ht using 1
    omega
  refine ⟨Store.ofState t,?_⟩
  convert BoundedExecutes.tracedCall full (by simp [RealSparse.program,hpc]) hs hbound using 1

theorem prepared_bound {B : ℕ} (m : ℕ) (s : Store) (hs : IndexBound B s.val)
    (hm : 100+6*m≤B) : IndexBound B (prepared m s).val := by
  unfold prepared
  exact (((((((hs.setIndex 58 0 (by omega)).setIndex 57 m (by omega)).setIndex 55 16
    (by omega)).setIndex 58 (m+m) (by omega)).setIndex 59 ((m+m)+(m+m))
    (by omega)).setIndex 56 ((m+m)+((m+m)+(m+m))) (by omega)).setIndex 58 100
    (by omega)).setIndex 56 ((m+m)+((m+m)+(m+m))+100) (by omega)

private theorem copy_literals {B : ℕ} (hB : 1≤B) :
    LiteralBound B (RealArrayCopy.program false) := by
  intro dst value h
  simp [RealArrayCopy.program] at h
  rcases h with h|h <;> omega

private theorem copy_advanced_bound {B src dst n k : ℕ} (v : ℕ→ℝ) (s : RAMState)
    (hs : IndexBound B s) (h : RealArrayCopy.Ready false src dst n k v s)
    (hk : k<n) (hsrc : src+n≤B) (hdst : dst+n≤B) :
    IndexBound B (RealArrayCopy.advanced s) := by
  have hs1 := hs.setIndex 2 (s.indices 2+1) (by rw [h.source]; omega)
  have hs2 := hs1.setIndex 3 (s.indices 3+1) (by rw [h.target]; omega)
  exact hs2.setIndex 0 (s.indices 0+1) (by rw [h.count]; omega)

private theorem copy_bounded_loop {B : ℕ} (input : RAMInput) (tape : ℕ→Bool)
    (hi : InputBound B input) (hB : 1≤B) (src dst n : ℕ) (v : ℕ→ℝ)
    (hsrc : 8≤src) (hsep : src+n≤dst) (hend : dst+n≤B)
    (remaining k : ℕ) (s : RAMState) (h : RealArrayCopy.Ready false src dst n k v s)
    (hc : k+remaining=n) (hs : IndexBound B s) :
    ∃ t, VisitedSteps ((RealArrayCopy.program false).next input tape)
      (IndexBound (2^30*B)) (8*remaining+1) s t ∧t.pc=13 ∧IndexBound B t := by
  have hl := copy_literals hB
  induction remaining generalizing k s with
  | zero =>
    have hk : k=n := by omega
    subst k
    let t : RAMState := {s with pc:=13}
    have step : (RealArrayCopy.program false).next input tape s=some t := by
      simp [Machine.next,RealArrayCopy.program,h.pc,h.count,h.total,t]
    have ht : IndexBound B t := hs
    exact ⟨t,.step (inflate hs) step (.refl (inflate ht)),rfl,ht⟩
  | succ remaining ih =>
    have hk : k<n := by omega
    have hb := copy_advanced_bound v s hs h hk (by omega) hend
    obtain ⟨t,ht,hpc,hbound⟩ := ih (k+1) (RealArrayCopy.advanced s)
      (RealArrayCopy.advanced_ready false src dst n k v s hsrc hsep h hk) (by omega) hb
    have cycleTrace := visited_index_bound hs hl hi le_rfl
      (execute_sound _ (RealArrayCopy.cycle false input tape src dst n k v s h hk))
    have cycleTrace' : VisitedSteps ((RealArrayCopy.program false).next input tape)
        (IndexBound (2^30*B)) 8 s (RealArrayCopy.advanced s) :=
      cycleTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
    refine ⟨t,?_,hpc,hbound⟩
    convert cycleTrace'.trans ht using 1
    omega

private theorem copy_bounded_from {B : ℕ} (input : RAMInput) (tape : ℕ→Bool)
    (hi : InputBound B input) (src dst n : ℕ) (s : Store) (hs : IndexBound B s.val)
    (hsrc : 8≤src) (hsep : src+n≤dst) (hend : dst+n≤B)
    (h55 : s.val.indices 55=src) (h56 : s.val.indices 56=dst)
    (h57 : s.val.indices 57=n) :
    ∃ t : Store, BoundedExecutes B 30 input tape (.call (RealArrayCopy.program false))
      (8*n+7) s t := by
  let v := fun j => s.val.words (src+j)
  have hready := RealArrayCopy.initialized_ready false src dst n v s.val hsrc s.property
    h55 h56 h57 (fun _ _ => rfl)
  have hinit : IndexBound B (RealArrayCopy.initialized false s.val) := by
    unfold RealArrayCopy.initialized
    exact (((hs.setIndex 0 0 (by omega)).setIndex 1 1 (by omega)).setIndex 2
      (s.val.indices 55) (hs 55)).setIndex 3 (s.val.indices 56) (hs 56)
  obtain ⟨t,ht,hpc,hbound⟩ := copy_bounded_loop input tape hi (by omega) src dst n v
    hsrc hsep hend n 0 (RealArrayCopy.initialized false s.val) hready (by omega) hinit
  have initTrace := visited_index_bound hs (copy_literals (by omega : 1≤B)) hi le_rfl
    (execute_sound _ (RealArrayCopy.initialize_steps false input tape s.val s.property))
  have initTrace' : VisitedSteps ((RealArrayCopy.program false).next input tape)
      (IndexBound (2^30*B)) 5 s.val (RealArrayCopy.initialized false s.val) :=
    initTrace.mono (fun _ hu => hu.mono (by norm_num; omega))
  have full : VisitedSteps ((RealArrayCopy.program false).next input tape)
      (IndexBound (2^30*B)) (8*n+6) s.val t := by
    convert initTrace'.trans ht using 1
    omega
  refine ⟨Store.ofState t,?_⟩
  convert BoundedExecutes.tracedCall full
    (by simp [RealArrayCopy.program,hpc]) hs hbound using 1

/-- The exact existing prefix runs from any bounded store. Its fixed-size
cycles return to the common cap, independently of the number of records. -/
theorem bounded_executes_from {B label : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (s : Store) (hs : IndexBound B s.val)
    (hroom : 100+8*es.length+label≤B)
    (entries : ∀e∈es,e.row≤label ∧e.column≤label) :
    ∃ t : Store, BoundedExecutes B 30 (input es vector) tape code
      (23*es.length+24) s t ∧IndexBound B t.val := by
  obtain ⟨a,ha⟩ := product_bounded_from es vector tape s hs hroom entries
  let b := prepared es.length a
  have hb : IndexBound B b.val := prepared_bound es.length a ha.finish (by omega)
  have entriesB : ∀e∈es,e.row≤B ∧e.column≤B := by
    intro e he
    have h := entries e he
    constructor <;> omega
  have hi := RealSparseOrder.source_input_bound es vector (by omega : es.length≤B) entriesB
  obtain ⟨t,ht⟩ := copy_bounded_from (input es vector) tape hi 16 (100+6*es.length)
    es.length b hb (by omega) (by omega) (by omega)
    (by simp [b,prepared,Store.ofState,RAMState.setIndex])
    (by simp [b,prepared,Store.ofState,RAMState.setIndex]; omega)
    (by simp [b,prepared,Store.ofState,RAMState.setIndex])
  refine ⟨t,?_,ht.finish⟩
  have hp : BoundedExecutes B 30 (input es vector) tape (.call prepare) 9 a b :=
    .atom (prepare_executes es vector tape a) (by omega) ha.finish hb
  convert ha.seq (hp.seq ht) using 1 <;> try rfl
  omega

theorem literal_bound {B : ℕ} (hB : 100≤B) : LiteralBound B code.compile := by
  have checked : code.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤100)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  exact (show value≤100 by simpa using hv).trans hB

/-- Every visited natural index word, including indirect addresses and the
final store, has at most thirty bits beyond the common boundary budget. -/
theorem resources_from_state {B label : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (s : Store) (hs : IndexBound B s.val)
    (hroom : 100+8*es.length+label≤B)
    (entries : ∀e∈es,e.row≤label ∧e.column≤label) :
    ∃ t : Store, Executes (input es vector) tape code (23*es.length+24) s t ∧
      VisitedSteps (program.next (input es vector) tape) (IndexWordWidth (30+B.size))
        (23*es.length+24) s.val (t.place code.size) ∧IndexBound B t.val := by
  obtain ⟨t,ht,hbound⟩ := bounded_executes_from es vector tape s hs hroom entries
  have entriesB : ∀e∈es,e.row≤B ∧e.column≤B := by
    intro e he
    have h := entries e he
    constructor <;> omega
  exact ⟨t,ht.executes,ht.word_width (literal_bound (by omega))
    (RealSparseOrder.source_input_bound es vector (by omega) entriesB),hbound⟩

/-- The bounded execution has precisely the same product and preserved
buffer as the existing correctness theorem. -/
theorem bounded_executes {B label : ℕ} (es : List SparseEntry) (vector : ℕ→ℝ)
    (tape : ℕ→Bool) (hroom : 100+8*es.length+label≤B)
    (entries : ∀e∈es,e.row≤label ∧e.column≤label) :
    ∃ t : Store, BoundedExecutes B 30 (input es vector) tape code
      (23*es.length+24) (Store.ofState RAMState.initial) t ∧
      (∀j<es.length,t.val.words (100+6*es.length+j)=RealSparse.transposeSum es vector j) ∧
      t.val.indices 55=16 ∧t.val.indices 56=100+6*es.length ∧t.val.indices 57=es.length ∧
      t.val.output=[] ∧t.val.indexOutput=[] ∧t.val.randomCursor=0 ∧IndexBound B t.val := by
  obtain ⟨t,ht,hq,h55,h56,h57,ho,hi,hr⟩ := executes es vector tape
  obtain ⟨u,hu,hbound⟩ := bounded_executes_from es vector tape (Store.ofState RAMState.initial)
    (by intro j; simp [Store.ofState,RAMState.initial]) hroom entries
  obtain ⟨_,rfl⟩ := ht.deterministic hu.executes
  exact ⟨t,hu,hq,h55,h56,h57,ho,hi,hr,hbound⟩

end Maxwell.Cost.RealTransposePreserve
