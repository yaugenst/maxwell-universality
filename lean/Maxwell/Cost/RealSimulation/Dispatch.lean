import Maxwell.Cost.RealSimulation.Compiler

/-! Actual finite dispatch and charged interpreter lifting. Instruction
contracts below are executions of the compiled instruction, not host effects. -/
namespace Maxwell.Cost.RealSimulation
open Control

/-- A selected instruction is preceded by three operations for each skipped
entry and four operations at the matching entry. Only dispatch scratch is
changed before the supplied actual instruction execution. -/
theorem dispatch_executes_at (L : Layout) (decoder : Code) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List BitRAMInstruction) (i j : ℕ) (hj : j < ops.length)
    (s t : Store) (cost : ℕ) (hpc : s.val.indices virtualPC = i + j)
    (hstep : Executes input tape (instruction L decoder (ops[j]'hj)) cost
      (s.put dispatchRegister (i + j)) t) :
    Executes input tape (dispatch L decoder i ops) (3 * j + 4 + cost) s t := by
  induction ops generalizing i j s with
  | nil => simp at hj
  | cons op ops ih =>
    cases j with
    | zero =>
      have hle : (s.put dispatchRegister i).val.indices virtualPC ≤
          (s.put dispatchRegister i).val.indices dispatchRegister := by
        simp [Store.put_indices, virtualPC, dispatchRegister] at hpc ⊢
        omega
      have hge : (s.put dispatchRegister i).val.indices dispatchRegister ≤
          (s.put dispatchRegister i).val.indices virtualPC := by
        simp [Store.put_indices, virtualPC, dispatchRegister] at hpc ⊢
        omega
      have leaf : Executes input tape (instruction L decoder op) cost (s.put dispatchRegister i) t := by
        simpa only [Nat.add_zero, List.getElem_cons_zero] using hstep
      have e := (literal_executes input tape s dispatchRegister i).seq
        (Executes.yes (no := dispatch L decoder (i + 1) ops) hle
          (Executes.yes (no := literal activeRegister 0) hge leaf))
      change Executes input tape
        (.seq (literal dispatchRegister i)
          (.branch virtualPC dispatchRegister
            (.branch dispatchRegister virtualPC (instruction L decoder op) (literal activeRegister 0))
            (dispatch L decoder (i + 1) ops))) _ s t
      convert e using 1
      omega
    | succ j =>
      have hj' : j < ops.length := by simpa using hj
      let middle := s.put dispatchRegister i
      have hpc' : middle.val.indices virtualPC = i + 1 + j := by
        simp only [middle, Store.put_indices, virtualPC, dispatchRegister, show (20 : ℕ) ≠ 12 by decide,
          ↓reduceIte]
        simp only [virtualPC] at hpc
        omega
      have leaf : Executes input tape (instruction L decoder (ops[j]'hj')) cost
          (middle.put dispatchRegister (i + 1 + j)) t := by
        simpa only [middle, Store.put_put, List.getElem_cons_succ,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
      have rest := ih (i + 1) j hj' middle hpc' leaf
      have test : ¬ middle.val.indices virtualPC ≤ middle.val.indices dispatchRegister := by
        simp only [middle, Store.put_indices, virtualPC, dispatchRegister,
          show (20 : ℕ) ≠ 12 by decide, ↓reduceIte]
        simp only [virtualPC] at hpc
        omega
      have e := (literal_executes input tape s dispatchRegister i).seq
        (Executes.no (yes := .branch dispatchRegister virtualPC
          (instruction L decoder op) (literal activeRegister 0)) test rest)
      change Executes input tape
        (.seq (literal dispatchRegister i)
          (.branch virtualPC dispatchRegister
            (.branch dispatchRegister virtualPC (instruction L decoder op) (literal activeRegister 0))
            (dispatch L decoder (i + 1) ops))) _ s t
      convert e using 1
      omega

/-- A caller's semantic relation need only ignore register 12. The total
dispatch overhead is bounded by the fixed source program length. -/
theorem dispatch_selected (L : Layout) (decoder : Code) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List BitRAMInstruction) (i j : ℕ) (hj : j < ops.length)
    (R Q : Store → Prop) (scratch : ∀ s v, R s → R (s.put dispatchRegister v))
    (bound : ℕ) (s : Store) (hs : R s) (hpc : s.val.indices virtualPC = i + j)
    (leaf : ∀ u, R u → ∃ cost t, cost ≤ bound ∧
      Executes input tape (instruction L decoder (ops[j]'hj)) cost u t ∧ Q t) :
    ∃ cost t, cost ≤ bound + 3 * (ops.length + 1) ∧
      Executes input tape (dispatch L decoder i ops) cost s t ∧ Q t := by
  obtain ⟨cost, t, hc, he, hq⟩ := leaf (s.put dispatchRegister (i + j)) (scratch _ _ hs)
  exact ⟨3 * j + 4 + cost, t, by omega,
    dispatch_executes_at L decoder input tape ops i j hj s t cost hpc he, hq⟩

/-- The inactive exit changes only the two dispatch-control registers. -/
structure DispatchFrame (s t : Store) : Prop where
  words : t.val.words = s.val.words
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  indexOutput : t.val.indexOutput = s.val.indexOutput
  indices : ∀ r, r ≠ activeRegister → r ≠ dispatchRegister → t.val.indices r = s.val.indices r

theorem DispatchFrame.refl (s : Store) : DispatchFrame s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem DispatchFrame.trans {s t u : Store} (h : DispatchFrame s t) (k : DispatchFrame t u) :
    DispatchFrame s u :=
  ⟨k.words.trans h.words, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output, k.indexOutput.trans h.indexOutput,
    fun r ha hd => (k.indices r ha hd).trans (h.indices r ha hd)⟩

theorem DispatchFrame.put (s : Store) (r v : ℕ)
    (hr : r = activeRegister ∨ r = dispatchRegister) : DispatchFrame s (s.put r v) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro q ha hd
  have hne : q ≠ r := by rcases hr with rfl | rfl <;> assumption
  simp only [Store.put_indices, hne, ↓reduceIte]

/-- An out-of-range source PC reaches the ordinary inactive literal after
traversing the finite dispatch list. -/
theorem dispatch_out_of_range (L : Layout) (decoder : Code) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List BitRAMInstruction) (i : ℕ) (s : Store)
    (hpc : i + ops.length ≤ s.val.indices virtualPC) :
    ∃ t, Executes input tape (dispatch L decoder i ops) (3 * ops.length + 2) s t ∧
      t.val.indices activeRegister = 0 ∧ DispatchFrame s t := by
  induction ops generalizing i s with
  | nil =>
    refine ⟨s.put activeRegister 0, ?_, by simp, DispatchFrame.put _ _ _ (Or.inl rfl)⟩
    simpa only [dispatch, List.length_nil, Nat.mul_zero, Nat.zero_add] using
      literal_executes input tape s activeRegister 0
  | cons op ops ih =>
    let middle := s.put dispatchRegister i
    have hpc' : i + 1 + ops.length ≤ middle.val.indices virtualPC := by
      simp only [middle, Store.put_indices, virtualPC, dispatchRegister,
        show (20 : ℕ) ≠ 12 by decide, ↓reduceIte]
      simp only [List.length_cons, virtualPC] at hpc
      omega
    obtain ⟨t, et, ht, hf⟩ := ih (i + 1) middle hpc'
    have test : ¬ middle.val.indices virtualPC ≤ middle.val.indices dispatchRegister := by
      simp only [middle, Store.put_indices, virtualPC, dispatchRegister,
        show (20 : ℕ) ≠ 12 by decide, ↓reduceIte]
      simp only [List.length_cons, virtualPC] at hpc
      omega
    refine ⟨t, ?_, ht, (DispatchFrame.put s _ _ (Or.inr rfl)).trans hf⟩
    have e := (literal_executes input tape s dispatchRegister i).seq
      (Executes.no (yes := .branch dispatchRegister virtualPC
        (instruction L decoder op) (literal activeRegister 0)) test et)
    change Executes input tape
      (.seq (literal dispatchRegister i)
        (.branch virtualPC dispatchRegister
          (.branch dispatchRegister virtualPC (instruction L decoder op) (literal activeRegister 0))
          (dispatch L decoder (i + 1) ops))) _ s t
    convert e using 1
    simp only [List.length_cons]
    omega

theorem dispatch_halt (L : Layout) (decoder : Code) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List BitRAMInstruction) (i j : ℕ) (hj : j < ops.length)
    (s : Store) (hpc : s.val.indices virtualPC = i + j) (hop : ops[j] = .halt) :
    ∃ t, Executes input tape (dispatch L decoder i ops) (3 * j + 6) s t ∧
      t.val.indices activeRegister = 0 ∧ DispatchFrame s t := by
  let middle := s.put dispatchRegister (i + j)
  let final := middle.put activeRegister 0
  have leaf : Executes input tape (instruction L decoder (ops[j]'hj)) 2 middle final := by
    rw [hop]
    exact literal_executes input tape middle activeRegister 0
  refine ⟨final, ?_, by simp [final],
    (DispatchFrame.put s _ _ (Or.inr rfl)).trans (DispatchFrame.put middle _ _ (Or.inl rfl))⟩
  simpa only [Nat.add_assoc] using
    dispatch_executes_at L decoder input tape ops i j hj s final 2 hpc leaf

/-- Both source halt cases are implemented by actual finite code and leave
all represented source data intact. -/
theorem dispatch_finish (L : Layout) (decoder : Code) (input : RAMInput)
    (tape : ℕ → Bool) (ops : List BitRAMInstruction) (s : Store)
    (halt : ops[s.val.indices virtualPC]? = none ∨
      ops[s.val.indices virtualPC]? = some .halt) :
    ∃ cost t, cost ≤ 3 * (ops.length + 1) ∧
      Executes input tape (dispatch L decoder 0 ops) cost s t ∧
      t.val.indices activeRegister = 0 ∧ DispatchFrame s t := by
  rcases halt with h | h
  · have hpc : ops.length ≤ s.val.indices virtualPC := List.getElem?_eq_none_iff.mp h
    obtain ⟨t, et, ht, hf⟩ := dispatch_out_of_range L decoder input tape ops 0 s (by omega)
    exact ⟨3 * ops.length + 2, t, by omega, et, ht, hf⟩
  · obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h
    obtain ⟨t, et, ht, hf⟩ := dispatch_halt L decoder input tape ops 0
      (s.val.indices virtualPC) hj s (by omega) he
    exact ⟨3 * s.val.indices virtualPC + 6, t, by omega, et, ht, hf⟩

/-- The final dispatch clears active, then the loop performs its final
false test. Both transitions are part of the actual instruction count. -/
theorem interpreter_finish (L : Layout) (decoder : Code) (M : BitRAM)
    (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (hone : s.val.indices oneRegister = 1) (hactive : s.val.indices activeRegister = 1)
    (halt : M.code[s.val.indices virtualPC]? = none ∨
      M.code[s.val.indices virtualPC]? = some .halt) :
    ∃ cost t, cost ≤ 3 * (M.code.length + 1) + 2 ∧
      Executes input tape (interpreter L decoder M) cost s t ∧
      t.val.indices activeRegister = 0 ∧ DispatchFrame s t := by
  obtain ⟨cost, t, hc, he, ht, hf⟩ := dispatch_finish L decoder input tape M.code s halt
  have hone' : t.val.indices oneRegister = 1 :=
    (hf.indices oneRegister (by decide) (by decide)).trans hone
  have done : Executes input tape (interpreter L decoder M) 1 t t := by
    apply Executes.done
    rw [hone', ht]
    omega
  exact ⟨1 + cost + 1, t, by omega,
    Executes.more (by rw [hone, hactive]) he done, ht, hf⟩

/-- A charged source execution lifts through actual dispatch contracts and
an actual terminal continuation. The loop test is paid at every iteration. -/
theorem interpreter_lift {σ : Type} (L : Layout) (decoder : Code) (M : BitRAM)
    (input : RAMInput) (tape : ℕ → Bool) (next : σ → Option (PricedStep σ))
    (R : σ → Store → Prop) (Q : Store → Prop) (C B : ℕ)
    (ready : ∀ a s, R a s → s.val.indices oneRegister = 1 ∧ s.val.indices activeRegister = 1)
    (step : ∀ a b extra s, next a = some ⟨b, extra⟩ → R a s →
      ∃ cost t, cost ≤ C * (extra + 1) ∧
        Executes input tape (dispatch L decoder 0 M.code) cost s t ∧ R b t)
    {n : ℕ} {a b : σ} (source : PricedSteps next n a b)
    (finish : ∀ s, R b s → ∃ cost t, cost ≤ B ∧
      Executes input tape (interpreter L decoder M) cost s t ∧ Q t)
    (s : Store) (hs : R a s) :
    ∃ cost t, cost ≤ (C + 1) * n + B ∧
      Executes input tape (interpreter L decoder M) cost s t ∧ Q t := by
  induction source generalizing s with
  | refl a => simpa using finish s hs
  | @step n extra a b c hnext rest ih =>
    obtain ⟨cost, t, hc, he, ht⟩ := step a b extra s hnext hs
    obtain ⟨restCost, u, hr, er, hu⟩ := ih finish t ht
    obtain ⟨hone, hactive⟩ := ready a s hs
    refine ⟨1 + cost + restCost, u, ?_, ?_, hu⟩
    · nlinarith
    · exact Executes.more (by rw [hone, hactive]) he er

end Maxwell.Cost.RealSimulation
