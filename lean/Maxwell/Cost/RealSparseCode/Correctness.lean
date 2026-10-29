import Maxwell.Cost.RealSparseCode.Cycle

namespace Maxwell.Cost.RealSparseCode
open RealSparse (execute execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem scan (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb n p B : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hcache : cb + 2 * n ≤ L.cache)
    (hbuffer : cb + 2 * n ≤ L.buffer)
    (hlabels : ∀ j < n, (rows j).size ≤ B ∧ (columns j).size ≤ B)
    (remaining : ℕ) (s : RAMState) (k : ℕ)
    (h : Ready s L rb cb n p k rows columns values) (hcount : k + remaining = n) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 210 + 46 * B) * remaining ∧
      Steps (program.next input tape) cost s t ∧ Ready t L rb cb n p n rows columns values ∧
      (∀ i, 17 ≤ i → t.words i = s.words i) ∧
      (∀ i, 47 ≤ i → RealNatAppend.Outside L i → t.indices i = s.indices i) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨0, s, by omega, Steps.refl s, h, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ remaining ih =>
    obtain ⟨c₁, t₁, hc₁, ht₁, hr₁, hw₁, hi₁, ho₁, hio₁, hrc₁⟩ :=
      cycle input tape L rb cb n p k rows columns values s hrb hcb hcache hbuffer h (by omega)
    obtain ⟨c₂, t₂, hc₂, ht₂, hr₂, hw₂, hi₂, ho₂, hio₂, hrc₂⟩ :=
      ih t₁ (k + 1) hr₁ (by omega)
    have hl := hlabels k (by omega)
    refine ⟨c₁ + c₂, t₂, ?_, ht₁.trans ht₂, hr₂,
      fun i hi => (hw₂ i hi).trans (hw₁ i hi),
      fun i hi hout => (hi₂ i hi hout).trans (hi₁ i hi hout),
      ho₂.trans ho₁, hio₂.trans hio₁, hrc₂.trans hrc₁⟩
    calc
      c₁ + c₂ ≤ (59 * p + 210 + 46 * B) + (59 * p + 210 + 46 * B) * remaining := by omega
      _ = (59 * p + 210 + 46 * B) * (remaining + 1) := by ring

/-- A fixed finite machine reads the ordered COO arrays and writes their
canonical natural/natural/rational stream into the addressed bit buffer. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb n p B : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ) (s : RAMState)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hcache : cb + 2 * n ≤ L.cache)
    (hbuffer : cb + 2 * n ≤ L.buffer)
    (hlabels : ∀ j < n, (rows j).size ≤ B ∧ (columns j).size ≤ B)
    (hpc : s.pc = 0) (hreal : s.indices 25 = rb) (hcoords : s.indices 28 = cb)
    (hn : s.indices 26 = n) (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (rb + j) = values j)
    (hco : ∀ j < n, s.indices (cb + 2 * j) = rows j ∧ s.indices (cb + 2 * j + 1) = columns j) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 210 + 46 * B) * n + 6 ∧ Terminates (program.next input tape) cost s t ∧
      t.pc = 263 ∧ StoredWord t L (word rows columns values p n) ∧
      t.indices 21 = L.bufferAt (word rows columns values p n).length ∧
      (∀ i, 17 ≤ i → t.words i = s.words i) ∧
      (∀ i, 47 ≤ i → RealNatAppend.Outside L i → t.indices i = s.indices i) ∧
      (∀ j < n, t.indices (cb + 2 * j) = rows j ∧ t.indices (cb + 2 * j + 1) = columns j) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor ∧
      t.indices 20 = L.cache ∧ t.indices 22 = L.stride ∧ t.indices 27 = p := by
  have hi := execute_sound _ (initialize_steps input tape s hpc)
  obtain ⟨cost, t, hcost, ht, hready, hw, hidx, ho, hio, hr⟩ :=
    scan input tape L rb cb n p B rows columns values hrb hcb hcache hbuffer hlabels n
      (initialized s) 0
      (initialized_ready L rb cb n p rows columns values s hcb hpc hreal hcoords hn hp hc hb hstride hv hco)
      (by omega)
  have hexit : Steps (program.next input tape) 1 t {t with pc := 263} := by
    apply execute_sound
    simp [execute, program, Machine.next, hready.pc, hready.total, hready.count]
  refine ⟨5 + cost + 1, {t with pc := 263}, by omega, ?_, rfl, hready.stored,
    hready.buffer, hw, ?_, hready.coordinates, ho, hio, hr, hready.cache, hready.stride, hready.precision⟩
  · exact ((hi.trans ht).trans hexit).terminates
      (Terminates.halt _ (by
        simp [program, RealRecordCode.program, RealNatAppend.program, RealNatCode.program,
          RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
          RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt,
          RealRatCode.program, Machine.next]))
  · intro i hi hout
    simpa [initialized, RAMState.setIndex, show i ≠ 40 by omega, show i ≠ 45 by omega,
      show i ≠ 46 by omega, show i ≠ 42 by omega, show i ≠ 43 by omega] using hidx i hi hout

theorem word_eq_flatMap (rows columns : ℕ → ℕ) (values : ℕ → ℝ) (p n : ℕ) :
    word rows columns values p n = (List.range n).flatMap
      (fun i => RealRecordCode.word (rows i) (columns i) (values i) p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [word, List.range_succ, ih]

end Maxwell.Cost.RealSparseCode
