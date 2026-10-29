import Maxwell.Cost.RealPrivate.Dispatch

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- A halt changes only dispatch scratch and the two completion flags.
All private typed source cells, input/output buffers, and log cells remain. -/
structure FinishFrame (s t : Store) : Prop where
  words : t.val.words = s.val.words
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  indexOutput : t.val.indexOutput = s.val.indexOutput
  indices : ∀ j, j ≠ dispatchRegister → j ≠ statusRegister → j ≠ activeRegister →
    t.val.indices j = s.val.indices j

theorem FinishFrame.refl (s : Store) : FinishFrame s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem FinishFrame.trans {s t u : Store} (h : FinishFrame s t) (k : FinishFrame t u) :
    FinishFrame s u :=
  ⟨k.words.trans h.words, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output, k.indexOutput.trans h.indexOutput,
    fun j hd hs ha => (k.indices j hd hs ha).trans (h.indices j hd hs ha)⟩

theorem FinishFrame.put (s : Store) (r v : ℕ)
    (hr : r = dispatchRegister ∨ r = statusRegister ∨ r = activeRegister) :
    FinishFrame s (s.put r v) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro j hd hs ha
  have hn : j ≠ r := by rcases hr with rfl | rfl | rfl <;> assumption
  simp only [Store.put_indices, hn, ↓reduceIte]

theorem FinishFrame.represents {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s t : Store} (f : FinishFrame s t) (h : Represents origin source written s.val) :
    Represents origin source written t.val := by
  have hi (j : ℕ) (hj : 256 ≤ j) : t.val.indices j = s.val.indices j :=
    f.indices j (by unfold dispatchRegister; omega) (by unfold statusRegister; omega)
      (by unfold activeRegister; omega)
  have hb (bank a : ℕ) : t.val.indices (slot origin bank a) = s.val.indices (slot origin bank a) :=
    hi _ (h.high.trans (slot_ge_origin origin bank a))
  refine ⟨h.high, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    f.randomCursor.trans h.random_cursor⟩
  · rw [f.indices originRegister (by decide) (by decide) (by decide)]; exact h.origin_word
  · rw [f.indices zeroRegister (by decide) (by decide) (by decide)]; exact h.zero
  · rw [f.indices oneRegister (by decide) (by decide) (by decide)]; exact h.one
  · rw [f.indices sourcePC (by decide) (by decide) (by decide)]; exact h.pc
  · intro a; rw [f.words]; exact h.words a
  · intro a; rw [hb]; exact h.indices a
  · rw [f.indices realOutputLength (by decide) (by decide) (by decide)]; exact h.real_output_length
  · rw [f.indices indexOutputLength (by decide) (by decide) (by decide)]; exact h.index_output_length
  · intro j hj; rw [f.words]; exact h.real_output j hj
  · intro j hj; rw [hb]; exact h.index_output j hj
  · rw [f.indices logLength (by decide) (by decide) (by decide)]; exact h.log_length
  · intro j hj; rw [hb]; exact h.log_cells j hj

theorem FinishFrame.inputs {L : Layout} {origin : ℕ} {B : InputBuffer} {input : RAMInput}
    {s t : Store} (f : FinishFrame s t) (h : Inputs L origin B input s.val) :
    Inputs L origin B input t.val := by
  refine ⟨?_, ?_, ?_, ?_, h.real_low, h.index_low, h.real_high, h.index_high,
    ?_, ?_, h.real_outside, h.index_outside⟩
  · rw [f.indices realInputBase (by decide) (by decide) (by decide)]; exact h.real_base
  · rw [f.indices realInputLength (by decide) (by decide) (by decide)]; exact h.real_length
  · rw [f.indices indexInputBase (by decide) (by decide) (by decide)]; exact h.index_base
  · rw [f.indices indexInputLength (by decide) (by decide) (by decide)]; exact h.index_length
  · intro j hj; rw [f.words]; exact h.real_cells j hj
  · intro j hj
    rw [f.indices _ (by have := h.index_low; unfold dispatchRegister; omega)
      (by have := h.index_low; unfold statusRegister; omega)
      (by have := h.index_low; unfold activeRegister; omega)]
    exact h.index_cells j hj

theorem finished_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape finished 4 s ((s.put statusRegister 1).put activeRegister 0) :=
  (literal_executes input tape s statusRegister 1).seq
    (literal_executes input tape _ activeRegister 0)

theorem finished_frame (s : Store) :
    FinishFrame s ((s.put statusRegister 1).put activeRegister 0) :=
  (FinishFrame.put s statusRegister 1 (Or.inr (Or.inl rfl))).trans
    (FinishFrame.put _ activeRegister 0 (Or.inr (Or.inr rfl)))

theorem dispatch_out_of_range (L : Layout) (input : RAMInput) (tape : ℕ → Bool)
    (ops : List RAMInstruction) (i : ℕ) (s : Store)
    (hpc : i+ops.length ≤ s.val.indices sourcePC) :
    ∃ t, Executes input tape (dispatch L i ops) (3*ops.length+4) s t ∧
      t.val.indices statusRegister = 1 ∧ t.val.indices activeRegister = 0 ∧ FinishFrame s t := by
  induction ops generalizing i s with
  | nil =>
      refine ⟨(s.put statusRegister 1).put activeRegister 0, ?_, ?_, by simp, finished_frame s⟩
      · exact finished_executes input tape s
      · simp [statusRegister, activeRegister]
  | cons op ops ih =>
      let middle := s.put dispatchRegister i
      have hpc' : i+1+ops.length ≤ middle.val.indices sourcePC := by
        simp only [middle, Store.put_indices, sourcePC, dispatchRegister,
          show (170 : ℕ) ≠ 8 by decide, ↓reduceIte]
        simp only [List.length_cons, sourcePC] at hpc
        omega
      obtain ⟨t, et, hs, ha, hf⟩ := ih (i+1) middle hpc'
      have test : ¬ middle.val.indices sourcePC ≤ middle.val.indices dispatchRegister := by
        simp only [middle, Store.put_indices, sourcePC, dispatchRegister,
          show (170 : ℕ) ≠ 8 by decide, ↓reduceIte]
        simp only [List.length_cons, sourcePC] at hpc
        omega
      refine ⟨t, ?_, hs, ha, (FinishFrame.put s _ _ (Or.inl rfl)).trans hf⟩
      have e := (literal_executes input tape s dispatchRegister i).seq
        (Executes.no (yes := .branch dispatchRegister sourcePC (instruction L op) finished) test et)
      change Executes input tape
        (.seq (literal dispatchRegister i)
          (.branch sourcePC dispatchRegister
            (.branch dispatchRegister sourcePC (instruction L op) finished)
            (dispatch L (i+1) ops))) _ s t
      convert e using 1
      simp only [List.length_cons]
      omega

theorem dispatch_halt (L : Layout) (input : RAMInput) (tape : ℕ → Bool)
    (ops : List RAMInstruction) (i j : ℕ) (hj : j < ops.length)
    (s : Store) (hpc : s.val.indices sourcePC = i+j) (hop : ops[j] = .halt) :
    ∃ t, Executes input tape (dispatch L i ops) (3*j+8) s t ∧
      t.val.indices statusRegister = 1 ∧ t.val.indices activeRegister = 0 ∧ FinishFrame s t := by
  let middle := s.put dispatchRegister (i+j)
  let final := (middle.put statusRegister 1).put activeRegister 0
  have leaf : Executes input tape (instruction L (ops[j]'hj)) 4 middle final := by
    rw [hop]
    exact finished_executes input tape middle
  refine ⟨final, ?_, ?_, by simp [final],
    (FinishFrame.put s _ _ (Or.inl rfl)).trans (finished_frame middle)⟩
  · simpa only [Nat.add_assoc] using dispatch_executes_at L input tape ops i j hj s final 4 hpc leaf
  · simp [final, statusRegister, activeRegister]

theorem dispatch_finish (L : Layout) (input : RAMInput) (tape : ℕ → Bool)
    (ops : List RAMInstruction) (s : Store)
    (halt : ops[s.val.indices sourcePC]? = none ∨ ops[s.val.indices sourcePC]? = some .halt) :
    ∃ cost t, cost ≤ 4*ops.length+4 ∧ Executes input tape (dispatch L 0 ops) cost s t ∧
      t.val.indices statusRegister = 1 ∧ t.val.indices activeRegister = 0 ∧ FinishFrame s t := by
  rcases halt with h | h
  · have hpc : ops.length ≤ s.val.indices sourcePC := List.getElem?_eq_none_iff.mp h
    obtain ⟨t, he, hs, ha, hf⟩ := dispatch_out_of_range L input tape ops 0 s (by omega)
    exact ⟨3*ops.length+4, t, by omega, he, hs, ha, hf⟩
  · obtain ⟨hj, hop⟩ := List.getElem?_eq_some_iff.mp h
    obtain ⟨t, he, hs, ha, hf⟩ := dispatch_halt L input tape ops 0
      (s.val.indices sourcePC) hj s (by omega) hop
    exact ⟨3*s.val.indices sourcePC+8, t, by omega, he, hs, ha, hf⟩

/-- The two actual `Machine.next = none` cases execute the finite finish
block and preserve the complete represented source and caller inputs. -/
theorem dispatch_next_none (M : Machine) (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source : RAMState} {written : List ℕ}
    (hnext : M.next sourceInput tape source = none)
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) :
    ∃ cost t, cost ≤ 4*M.code.length+4 ∧
      Executes externalInput tape (dispatch L 0 M.code) cost s t ∧
      Represents origin source written t.val ∧ Inputs L origin B sourceInput t.val ∧
      t.val.indices statusRegister = 1 ∧ t.val.indices activeRegister = 0 ∧ FinishFrame s t := by
  have halt : M.code[source.pc]? = none ∨ M.code[source.pc]? = some .halt := by
    cases hc : M.code[source.pc]? with
    | none => exact Or.inl rfl
    | some op =>
      right
      cases op <;> simp only [Machine.next, hc, reduceCtorEq] at hnext
      rfl
  rw [← h.pc] at halt
  obtain ⟨cost, t, hc, he, hs, ha, hf⟩ := dispatch_finish L externalInput tape M.code s halt
  exact ⟨cost, t, hc, he, hf.represents h, hf.inputs hi, hs, ha, hf⟩

end Maxwell.Cost.RealPrivate
