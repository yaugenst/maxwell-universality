import Maxwell.Cost.RealSparseOrder.Buffer

namespace Maxwell.Cost.RealSparseOrder.Load
open RealSparse (execute execute_sound execute_add entryAt input)

set_option maxRecDepth 20000

def program : Machine := ⟨[
  .indexLiteral 0 0,.indexLiteral 1 1,.indexLiteral 2 2,.inputIndex 3 0,
  .indexLiteral 4 0,.indexLiteral 5 1,.indexLiteral 6 100,.indexLiteral 9 100,
  .branchIndexLE 3 4 22 9,.inputIndex 7 5,.storeIndex 6 7,.indexAdd 5 5 1,
  .inputIndex 7 5,.indexAdd 8 6 1,.storeIndex 8 7,.input 0 4,.store 9 0,
  .indexAdd 5 5 1,.indexAdd 6 6 2,.indexAdd 9 9 1,.indexAdd 4 4 1,
  .jump 8,.halt]⟩

def Ready (s : RAMState) (m k : ℕ) : Prop :=
  s.pc=8 ∧ s.indices 0=0 ∧ s.indices 1=1 ∧ s.indices 2=2 ∧ s.indices 3=m ∧
    s.indices 4=k ∧ s.indices 5=1+2*k ∧ s.indices 6=100+2*k ∧ s.indices 9=100+k

noncomputable def initialized (m : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 2
  let s := s.setIndex 3 m
  let s := s.setIndex 4 0
  let s := s.setIndex 5 1
  let s := s.setIndex 6 100
  s.setIndex 9 100

theorem initialize_steps (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    execute (program.next (input es vector) tape) 8 RAMState.initial = some (initialized es.length) := by
  simp [execute,program,Machine.next,RAMState.initial,RAMState.setIndex,initialized]

theorem initialized_ready (m : ℕ) : Ready (initialized m) m 0 := by
  simp [Ready,initialized,RAMState.initial,RAMState.setIndex]

noncomputable def middle (s : RAMState) (e : SparseEntry) : RAMState :=
  let t := ({s with pc := 9}).setIndex 7 e.row
  let t := t.setIndex (s.indices 6) e.row
  let t := t.setIndex 5 (s.indices 5+1)
  let t := t.setIndex 7 e.column
  let t := t.setIndex 8 (s.indices 6+1)
  t.setIndex (s.indices 6+1) e.column

noncomputable def advanced (s : RAMState) (e : SparseEntry) : RAMState :=
  let t := (middle s e).setWord 0 e.value
  let t := t.setWord (s.indices 9) e.value
  let t := t.setIndex 5 (s.indices 5+2)
  let t := t.setIndex 6 (s.indices 6+2)
  let t := t.setIndex 9 (s.indices 9+1)
  let t := t.setIndex 4 (s.indices 4+1)
  {t with pc := 8}

set_option maxHeartbeats 1400000 in
theorem cycle (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (hr : Ready s es.length k) (hk : k < es.length) :
    execute (program.next (input es vector) tape) 14 s = some (advanced s (entryAt es k)) := by
  rcases hr with ⟨hpc,h0,h1,h2,hm,hi,ha,hc,hv⟩
  have hn : ¬es.length ≤ k := by omega
  have hrow : ∀ j : ℕ, j < 10 → j ≠ 100+2*k := by omega
  have hcol : ∀ j : ℕ, j < 10 → j ≠ 100+2*k+1 := by omega
  have he : execute (program.next (input es vector) tape) 7 s = some (middle s (entryAt es k)) := by
    simp (config := {maxSteps := 100000}) [execute,program,Machine.next,hpc,h1,hm,hi,ha,hc,hn,
      RAMState.setIndex,middle,hrow,RealSparse.input_row,RealSparse.input_column,
      show 1+2*k+1=2+2*k by omega]
  rw [show 14=7+7 from rfl,execute_add,he,Option.bind_some]
  simp (config := {maxSteps := 100000}) [execute,program,Machine.next,advanced,middle,RAMState.setIndex,
    RAMState.setWord,h1,h2,hi,ha,hc,hv,hrow,hcol,RealSparse.input_value,hk]

theorem advanced_ready (s : RAMState) (m k : ℕ) (h : Ready s m k) (e : SparseEntry) :
    Ready (advanced s e) m (k+1) := by
  rcases h with ⟨hpc,h0,h1,h2,hm,hi,ha,hc,hv⟩
  have hrow : ∀ j : ℕ, j < 10 → j ≠ 100+2*k := by omega
  have hcol : ∀ j : ℕ, j < 10 → j ≠ 100+2*k+1 := by omega
  simp [Ready,advanced,middle,RAMState.setIndex,RAMState.setWord,h0,h1,h2,hm,hi,ha,hc,hv,hrow,hcol]
  omega

theorem advanced_row (s : RAMState) (m k j : ℕ) (h : Ready s m k) (e : SparseEntry) :
    (advanced s e).indices (100+2*j) = if j=k then e.row else s.indices (100+2*j) := by
  have hc := h.2.2.2.2.2.2.2.1
  have hlarge : ∀ a : ℕ, a < 10 → 100+2*j ≠ a := by omega
  have hodd : 100+2*j ≠ 100+2*k+1 := by omega
  by_cases he : j=k
  · subst j
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hc,hlarge]
  · have hd : 100+2*j ≠ 100+2*k := by omega
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hc,hlarge,hodd,he]

theorem advanced_column (s : RAMState) (m k j : ℕ) (h : Ready s m k) (e : SparseEntry) :
    (advanced s e).indices (100+2*j+1) = if j=k then e.column else s.indices (100+2*j+1) := by
  have hc := h.2.2.2.2.2.2.2.1
  have hlarge : ∀ a : ℕ, a < 10 → 100+2*j+1 ≠ a := by omega
  have heven : 100+2*j+1 ≠ 100+2*k := by omega
  by_cases he : j=k
  · subst j
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hc,hlarge]
  · have hd : 100+2*j+1 ≠ 100+2*k+1 := by omega
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hc,hlarge,heven,he]

theorem advanced_value (s : RAMState) (m k j : ℕ) (h : Ready s m k) (e : SparseEntry) :
    (advanced s e).words (100+j) = if j=k then e.value else s.words (100+j) := by
  have hv := h.2.2.2.2.2.2.2.2
  by_cases he : j=k
  · subst j
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hv]
  · have hd : 100+j ≠ 100+k := by omega
    simp [advanced,middle,RAMState.setIndex,RAMState.setWord,hv,he]

theorem advanced_stored (es : List SparseEntry) (s : RAMState) (k : ℕ)
    (hr : Ready s es.length k) (hs : StoredPrefix initialBuffer s es k) :
    StoredPrefix initialBuffer (advanced s (entryAt es k)) es (k+1) := by
  intro j hj
  simp only [initialBuffer,Buffer.row,Buffer.column,Buffer.value]
  rw [advanced_row s _ k j hr,advanced_column s _ k j hr,advanced_value s _ k j hr]
  by_cases he : j=k
  · subst j; simp
  · have hlt : j<k := by omega
    simpa [he,initialBuffer,Buffer.row,Buffer.column,Buffer.value] using hs j hlt

/-- Loading is an actual finite scan; the input COO records are never
repackaged as a second input tape. -/
theorem loop (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool)
    (remaining k : ℕ) (s : RAMState) (hr : Ready s es.length k)
    (hc : k+remaining=es.length) (hs : StoredPrefix initialBuffer s es k) :
    ∃ t, Terminates (program.next (input es vector) tape) (14*remaining+1) s t ∧
      t.pc=22 ∧ Stored initialBuffer t es ∧ t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
      t.indexOutput=s.indexOutput := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k=es.length := by omega
    subst k
    let t : RAMState := {s with pc := 22}
    have step : program.next (input es vector) tape s = some t := by
      simp [Machine.next,program,hr.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1,t]
    refine ⟨t,Terminates.step step (Terminates.halt t ?_),rfl,hs,rfl,rfl,rfl⟩
    simp [program,Machine.next,t]
  | succ remaining ih =>
    have hk : k<es.length := by omega
    obtain ⟨t,et,hpc,ht,hrandom,hout,hindices⟩ := ih (k+1) (advanced s (entryAt es k))
      (advanced_ready s _ k hr _) (by omega) (advanced_stored es s k hr hs)
    refine ⟨t,?_,hpc,ht,hrandom,hout,hindices⟩
    convert (execute_sound _ (cycle es vector tape s k hr hk)).terminates et using 1
    omega

theorem terminates (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t, Terminates (program.next (input es vector) tape) (14*es.length+9) RAMState.initial t ∧
      t.pc=22 ∧ Stored initialBuffer t es ∧ t.randomCursor=0 ∧ t.output=[] ∧ t.indexOutput=[] := by
  obtain ⟨t,et,hpc,ht,hr,ho,hi⟩ := loop es vector tape es.length 0 (initialized es.length)
    (initialized_ready _) (by omega) (by intro j hj; omega)
  refine ⟨t,?_,hpc,ht,hr,ho,hi⟩
  convert (execute_sound _ (initialize_steps es vector tape)).terminates et using 1
  omega

/-- This loader is a callable prefix of the same finite encoder. -/
theorem executes (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t : RealSimulation.Control.Store,
      RealSimulation.Control.Executes (input es vector) tape (.call program) (14*es.length+10)
        (RealSimulation.Control.Store.ofState RAMState.initial) t ∧
      Stored initialBuffer t.val es ∧ t.val.randomCursor=0 ∧ t.val.output=[] ∧ t.val.indexOutput=[] := by
  obtain ⟨t,et,hpc,ht,hr,ho,hi⟩ := terminates es vector tape
  refine ⟨RealSimulation.Control.Store.ofState t,?_,ht,hr,ho,hi⟩
  convert RealSimulation.Control.Executes.call program
    (RealSimulation.Control.Store.ofState RAMState.initial) t (14*es.length+9)
    et.toSteps (by simp [program,hpc]) using 1

theorem run (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t, (program.run (input es vector) tape (14*es.length+10)).finished=some t ∧
      (program.run (input es vector) tape (14*es.length+10)).instructions=14*es.length+9 ∧
      Stored initialBuffer t es := by
  obtain ⟨t,et,_,ht,_⟩ := terminates es vector tape
  obtain ⟨hr,hc⟩ := runCapped_of_terminates _ et
  exact ⟨t,hr,hc,ht⟩

end Maxwell.Cost.RealSparseOrder.Load
