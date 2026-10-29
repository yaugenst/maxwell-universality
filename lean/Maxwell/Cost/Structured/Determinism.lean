import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.Structured

/-- Two terminating executions of the same finite program on the same
stored input have identical charged costs and final stores. -/
theorem Executes.deterministic {input : List Bool} {randomTape : ℕ → Bool}
    {code : Code} {a b : ℕ} {s t u : Store}
    (first : Executes input randomTape code a s t)
    (second : Executes input randomTape code b s u) : a = b ∧ t = u := by
  have ht := first.compiled_run (a+b+1) (by omega)
  have hu := second.compiled_run (a+b+1) (by omega)
  refine ⟨ht.2.symm.trans hu.2, ?_⟩
  have hplace : t.place code.size = u.place code.size :=
    Option.some.inj (ht.1.symm.trans hu.1)
  have hstore := congrArg Store.ofState hplace
  have reset (v : Store) : Store.ofState (v.place code.size) = v := by
    apply Subtype.ext
    change { v.val with pc := 0 } = v.val
    cases v with
    | mk val hv =>
      cases val
      cases hv
      rfl
  simpa only [reset] using hstore

end Maxwell.Cost.Structured
