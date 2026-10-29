import Maxwell.Cost.RealPrivate.InstructionSimulation

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- A selected instruction is preceded by three operations for each skipped
entry and four operations at the matching entry. Only dispatch scratch is
changed before the supplied actual instruction execution. -/
theorem dispatch_executes_at (L : Layout) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List RAMInstruction) (i j : ℕ) (hj : j < ops.length)
    (s t : Store) (cost : ℕ) (hpc : s.val.indices sourcePC = i + j)
    (hstep : Executes input tape (instruction L (ops[j]'hj)) cost
      (s.put dispatchRegister (i + j)) t) :
    Executes input tape (dispatch L i ops) (3 * j + 4 + cost) s t := by
  induction ops generalizing i j s with
  | nil => simp at hj
  | cons op ops ih =>
    cases j with
    | zero =>
      have hle : (s.put dispatchRegister i).val.indices sourcePC ≤
          (s.put dispatchRegister i).val.indices dispatchRegister := by
        simp [Store.put_indices, sourcePC, dispatchRegister] at hpc ⊢
        omega
      have hge : (s.put dispatchRegister i).val.indices dispatchRegister ≤
          (s.put dispatchRegister i).val.indices sourcePC := by
        simp [Store.put_indices, sourcePC, dispatchRegister] at hpc ⊢
        omega
      have leaf : Executes input tape (instruction L op) cost (s.put dispatchRegister i) t := by
        simpa only [Nat.add_zero, List.getElem_cons_zero] using hstep
      have e := (literal_executes input tape s dispatchRegister i).seq
        (Executes.yes (no := dispatch L (i + 1) ops) hle
          (Executes.yes (no := finished) hge leaf))
      change Executes input tape
        (.seq (literal dispatchRegister i)
          (.branch sourcePC dispatchRegister
            (.branch dispatchRegister sourcePC (instruction L op) finished)
            (dispatch L (i + 1) ops))) _ s t
      convert e using 1
      omega
    | succ j =>
      have hj' : j < ops.length := by simpa using hj
      let middle := s.put dispatchRegister i
      have hpc' : middle.val.indices sourcePC = i + 1 + j := by
        simp only [middle, Store.put_indices, sourcePC, dispatchRegister, show (170 : ℕ) ≠ 8 by decide,
          ↓reduceIte]
        simp only [sourcePC] at hpc
        omega
      have leaf : Executes input tape (instruction L (ops[j]'hj')) cost
          (middle.put dispatchRegister (i + 1 + j)) t := by
        simpa only [middle, Store.put_put, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
      have rest := ih (i + 1) j hj' middle hpc' leaf
      have test : ¬ middle.val.indices sourcePC ≤ middle.val.indices dispatchRegister := by
        simp only [middle, Store.put_indices, sourcePC, dispatchRegister,
          show (170 : ℕ) ≠ 8 by decide, ↓reduceIte]
        simp only [sourcePC] at hpc
        omega
      have e := (literal_executes input tape s dispatchRegister i).seq
        (Executes.no (yes := .branch dispatchRegister sourcePC
          (instruction L op) finished) test rest)
      change Executes input tape
        (.seq (literal dispatchRegister i)
          (.branch sourcePC dispatchRegister
            (.branch dispatchRegister sourcePC (instruction L op) finished)
            (dispatch L (i + 1) ops))) _ s t
      convert e using 1
      omega

/-- A successful actual source step selects its literal compiled branch.
The fixed dispatch overhead is charged in addition to the instruction bound. -/
theorem dispatch_next (M : Machine) (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source next : RAMState} {written : List ℕ}
    (op : RAMInstruction) (hcode : M.code[source.pc]? = some op)
    (hnext : M.next sourceInput tape source = some next)
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) :
    ∃ cost t, cost ≤ 4*M.code.length+instructionBound L ∧
      Executes externalInput tape (dispatch L 0 M.code) cost s t ∧
      Represents origin next (recorded op source written) t.val ∧ CallerFrame origin s.val t.val := by
  obtain ⟨hj, hop⟩ := List.getElem?_eq_some_iff.mp hcode
  let middle := s.put dispatchRegister source.pc
  have hm : Represents origin source written middle.val :=
    h.put_scratch dispatchRegister source.pc (by
      simp [ProtectedIndex, dispatchRegister, zeroRegister, oneRegister])
  have hf : CallerFrame origin s.val middle.val :=
    callerFrame_put s origin dispatchRegister source.pc (Or.inl (by decide))
  have him : Inputs L origin B sourceInput middle.val := hf.inputs h.high hi
  obtain ⟨cost, t, hc, he, ht, hframe⟩ :=
    instruction_next M externalInput sourceInput tape op hcode hnext middle hm him
  have hleaf : Executes externalInput tape (instruction L (M.code[source.pc]'hj)) cost
      (s.put dispatchRegister (0+source.pc)) t := by
    simpa only [hop, Nat.zero_add] using he
  have hex := dispatch_executes_at L externalInput tape M.code 0 source.pc hj s t cost
    (by simpa only [Nat.zero_add] using h.pc) hleaf
  exact ⟨3*source.pc+4+cost, t, by omega, hex, ht, hf.trans hframe⟩

end Maxwell.Cost.RealPrivate
