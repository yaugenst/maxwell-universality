import Maxwell.Cost.RealArrayCode.Cycle

namespace Maxwell.Cost.RealArrayCode
open RealSparse (execute execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

theorem scan (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (hbase : 32 ≤ base)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : Ready s L base n p k v)
    (hcount : k + remaining = n) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 167) * remaining ∧ Steps (program.next input tape) cost s t ∧
      Ready t L base n p n v ∧ t.output = s.output ∧ t.indexOutput = s.indexOutput ∧
      t.randomCursor = s.randomCursor ∧ (∀ i, Outside L i → t.indices i = s.indices i) := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨0, s, by omega, Steps.refl s, h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | succ remaining ih =>
    obtain ⟨c₁, t₁, hc₁, ht₁, hr₁, ho₁, hio₁, hcurs₁, hf₁⟩ :=
      cycle input tape L base n p k v s hbase h (by omega)
    obtain ⟨c₂, t₂, hc₂, ht₂, hr₂, ho₂, hio₂, hcurs₂, hf₂⟩ :=
      ih t₁ (k + 1) hr₁ (by omega)
    refine ⟨c₁ + c₂, t₂, ?_, ht₁.trans ht₂, hr₂, ho₂.trans ho₁, hio₂.trans hio₁,
      hcurs₂.trans hcurs₁, fun i hi => (hf₂ i hi).trans (hf₁ i hi)⟩
    calc
      c₁ + c₂ ≤ (59 * p + 167) + (59 * p + 167) * remaining := Nat.add_le_add hc₁ hc₂
      _ = (59 * p + 167) * (remaining + 1) := by ring

/-- The actual array contents are consumed by charged loads and rounded
one entry at a time. The final buffer contains the entire rational stream. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hs : s.indices 24 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 167) * n + 3 ∧ Terminates (program.next input tape) cost s t ∧
      t.pc = 171 ∧ StoredWord t L (word v p n) ∧
      t.indices 21 = L.bufferAt (word v p n).length ∧
      (∀ j < n, t.words (base + j) = v j) ∧ t.output = s.output ∧
      t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor ∧
      (∀ i, Outside L i → t.indices i = s.indices i) := by
  have hi := execute_sound _ (initialize_steps input tape s hpc)
  obtain ⟨cost, t, hcost, ht, hready, ho, hio, hr, hframe⟩ :=
    scan input tape L base n p v hbase n (initialized s) 0
      (initialized_ready L base n p v s hpc hs hn hp hc hb hstride hv) (by omega)
  have hexit : Steps (program.next input tape) 1 t {t with pc := 171} := by
    apply execute_sound
    simp [execute, program, Machine.next, hready.pc, hready.total, hready.count]
  refine ⟨2 + cost + 1, {t with pc := 171}, by omega, ?_, rfl, hready.stored,
    hready.buffer, hready.values, ho, hio, hr, ?_⟩
  · exact ((hi.trans ht).trans hexit).terminates
      (Terminates.halt _ (by
        simp [program, RealRoundRat.program, RealMidpointRegister.program,
          RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program,
          RealMidpointRegister.adapt, RealRatCode.program, RealNatCode.program, Machine.next]))
  · intro i hi
    simpa [initialized, RAMState.setIndex, show i ≠ 23 by have := hi.1; omega,
      show i ≠ 28 by have := hi.1; omega] using hframe i hi

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hs : s.indices 24 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) ((59 * p + 167) * n + 4) s).finished = some t ∧
      (runCapped (program.next input tape) ((59 * p + 167) * n + 4) s).instructions ≤
        (59 * p + 167) * n + 3 ∧ StoredWord t L (word v p n) := by
  obtain ⟨cost, t, hbound, ht, _, hstored, _⟩ :=
    terminates input tape L base n p v s hbase hpc hs hn hp hc hb hstride hv
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates_ge _ ht ((59 * p + 167) * n + 4) (by omega)
  exact ⟨t, hf, hcost.le.trans hbound, hstored⟩

theorem word_eq_flatMap (v : ℕ → ℝ) (p n : ℕ) :
    word v p n = (List.range n).flatMap (fun i => Codec.rat (RealMidpoint.approximation (v i) p)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [word, List.range_succ, ih]

end Maxwell.Cost.RealArrayCode
