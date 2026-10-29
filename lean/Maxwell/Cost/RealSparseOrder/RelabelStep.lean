import Maxwell.Cost.RealSparseOrder.RelabelState

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

def chooseCode : Code :=
  .branch 36 0 (.call createProgram)
    (.branch 37 34 (.branch 34 37 .skip (.call createProgram)) (.call createProgram))

noncomputable def chosen (input : RAMInput) (previous : Option ℕ) (row : ℕ) (s : Store) : Store :=
  if previous=some row then s else Store.ofState (created input s.val)

theorem choose_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (previous : Option ℕ) (row : ℕ) (h0 : s.val.indices 0=0)
    (hp : s.val.indices 34=previous.getD 0)
    (hs : s.val.indices 36=if previous.isSome then 1 else 0)
    (hr : s.val.indices 37=row) (hready : CreateReady s.val) :
    ∃cost,cost≤13 ∧Executes input tape chooseCode cost s (chosen input previous row s) := by
  have run := create_executes input tape s hready
  cases previous with
  | none =>
    refine ⟨11,by omega,?_⟩
    exact Executes.yes (by simp only [hs,h0]; decide) run
  | some old =>
    have hseen : ¬s.val.indices 36≤s.val.indices 0 := by simp [hs,h0]
    by_cases he : old=row
    · subst old
      refine ⟨4,by omega,?_⟩
      rw [chosen,ite_eq_left rfl]
      exact Executes.no hseen (Executes.yes (show s.val.indices 37≤s.val.indices 34 by simp [hp,hr])
        (Executes.yes (show s.val.indices 34≤s.val.indices 37 by simp [hp,hr]) (Executes.skip s)))
    · have hc : chosen input (some old) row s=Store.ofState (created input s.val) := by
        simp [chosen,he]
      rw [hc]
      by_cases hle : row≤old
      · refine ⟨13,by omega,?_⟩
        exact Executes.no hseen (Executes.yes (by simpa [hp,hr] using hle)
          (Executes.no (by simp only [hp,hr,Option.getD_some]; omega) run))
      · refine ⟨12,by omega,?_⟩
        exact Executes.no hseen (Executes.no (by simpa [hp,hr] using hle) run)

def body : Code := .seq (.call loadProgram) (.seq chooseCode (.call rewriteProgram))
def loopCode : Code := .loop 1 32 body

noncomputable def processed (input : RAMInput) (previous : Option ℕ) (row : ℕ) (s : Store) : Store :=
  Store.ofState (rewritten (chosen input previous row (Store.ofState (loaded s.val))).val)

theorem Config.chosen {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hm : 100≤map) (hr : s.val.indices 37=row) :
    Config (chosen input previous row s).val b remaining (some row)
      (nextCount previous count row) m map rhs := by
  by_cases he : previous=some row
  · simpa only [Relabel.chosen,nextCount,he,ite_true] using h
  · simp only [Relabel.chosen,nextCount,he,ite_false,config_ofState]
    exact h.created hm hr

theorem processed_config {input : RAMInput} {s : Store} {b : Buffer} {remaining : ℕ}
    {previous : Option ℕ} {count m map rhs row : ℕ}
    (h : Config s.val b remaining previous count m map rhs)
    (hb : 100≤b.coordinates) (hm : 100≤map) (hr : s.val.indices b.coordinates=row) :
    Config (processed input previous row s).val (b.shift 1) (remaining-1) (some row)
      (nextCount previous count row) m map rhs := by
  have hl : Config (Store.ofState (loaded s.val)).val b remaining previous count m map rhs :=
    (config_ofState _ _ _ _ _ _ _ _).mpr h.loaded
  have he : (Store.ofState (loaded s.val)).val.indices 37=row := by
    simp [loaded,RAMState.setIndex,Store.ofState,h.cursor,hr]
  exact (config_ofState _ _ _ _ _ _ _ _).mpr ((hl.chosen hm he).rewritten hb)

/-- The largest branch reads a new row, writes its map and RHS, and then
rewrites the record's row label. Every operation is actual finite code. -/
theorem step (input : RAMInput) (tape : ℕ→Bool) (s : Store) (b : Buffer)
    (remaining : ℕ) (previous : Option ℕ) (count m map rhs row : ℕ)
    (h : Config s.val b remaining previous count m map rhs)
    (hb : 100≤b.coordinates) (hm : 100≤map) (hv : 100≤rhs)
    (hr : s.val.indices b.coordinates=row) :
    ∃cost,cost≤20 ∧Executes input tape body cost s (processed input previous row s) := by
  let mid := Store.ofState (loaded s.val)
  have hc : Config mid.val b remaining previous count m map rhs :=
    (config_ofState _ _ _ _ _ _ _ _).mpr h.loaded
  have he : mid.val.indices 37=row := by
    simp [mid,loaded,RAMState.setIndex,Store.ofState,h.cursor,hr]
  obtain ⟨cost,hcost,run⟩ := choose_executes input tape mid previous row hc.zero
    hc.previousValue hc.seen he (hc.create_ready hm hv)
  have hchosen := hc.chosen (input:=input) hm he
  refine ⟨2+(cost+5),by omega,?_⟩
  exact Executes.seq (load_executes input tape s)
    (Executes.seq run (rewrite_executes input tape _ (hchosen.rewrite_ready hb)))

end Maxwell.Cost.RealSparseOrder.Relabel
