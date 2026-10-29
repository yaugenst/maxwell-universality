import Maxwell.Cost.Structured.Correctness
import Maxwell.Cost.Link

namespace Maxwell.Cost.Structured

def Store.renameTapes (p : Equiv.Perm ℕ) (s : Store) : Store :=
  ⟨s.val.renameTapes p, s.property⟩

/-- A fixed work-tape renaming reuses verified finite code. The extra
operation is the actual return from the renamed compiled fragment. -/
theorem Executes.renamed_call {input : List Bool} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store} (h : Executes input randomTape code cost s t)
    (p : Equiv.Perm ℕ) :
    Executes input randomTape (.call (code.compile.renameTapes p)) (cost+1)
      (s.renameTapes p) (t.renameTapes p) := by
  have hs := h.compiled_steps.renameTapes p
  have hh : (code.compile.renameTapes p).code[((t.place code.size).renameTapes p).pc]? = some .halt := by
    simp [BitRAM.renameTapes, BitRAMState.renameTapes, Store.place,
      code.compile_halt, BitRAMInstruction.renameTapes]
  convert Executes.call _ (s.renameTapes p) _ _ hs hh using 1
  apply Subtype.ext
  simp [Store.ofState, Store.renameTapes, Store.place, BitRAMState.renameTapes, t.property]

theorem Store.renameTapes_symm (p : Equiv.Perm ℕ) (s : Store) :
    (s.renameTapes p.symm).renameTapes p = s := by
  apply Subtype.ext
  simp [Store.renameTapes, BitRAMState.renameTapes, Function.comp_def]

end Maxwell.Cost.Structured
