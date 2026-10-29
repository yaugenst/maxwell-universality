import Maxwell.Cost.RealSparseCode.Program

namespace Maxwell.Cost.RealSparseCode
open RealNatCode (Layout StoredWord)
open RealSparse (execute_sound)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem cycle (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb n p k : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ) (s : RAMState)
    (hrb : 32 ≤ rb) (hcb : 64 ≤ cb) (hcache : cb + 2 * n ≤ L.cache)
    (hbuffer : cb + 2 * n ≤ L.buffer) (h : Ready s L rb cb n p k rows columns values) (hk : k < n) :
    ∃ cost : ℕ, ∃ final : RAMState,
      cost ≤ 59 * p + 210 + 23 * ((rows k).size + (columns k).size) ∧
      Steps (program.next input tape) cost s final ∧ Ready final L rb cb n p (k + 1) rows columns values ∧
      (∀ i, 17 ≤ i → final.words i = s.words i) ∧
      (∀ i, 47 ≤ i → RealNatAppend.Outside L i → final.indices i = s.indices i) ∧
      final.output = s.output ∧ final.indexOutput = s.indexOutput ∧ final.randomCursor = s.randomCursor := by
  let L' := L.shiftBuffer (word rows columns values p k).length
  obtain ⟨cost, t, hcost, ht, htpc, hstored, hcursor, hwords, hindices, ho, hio, hrandom⟩ :=
    RealRecordCode.terminates input tape L' (rows k) (columns k) (values k) p {loaded s with pc := 0} rfl
      (by simp [loaded, RAMState.setWord, RAMState.setIndex, h.coordinatePointer, (h.coordinates k hk).1])
      (by simp [loaded, RAMState.setWord, RAMState.setIndex, h.coordinatePointer, (h.coordinates k hk).2])
      (by simp [loaded, RAMState.setWord, h.realPointer, h.coefficients k hk])
      h.precision h.cache h.buffer h.stride
  have hcall := contains_record.call_at input tape (loaded s) t rfl ht.toSteps (by
    simp [RealRecordCode.program, RealNatAppend.program, RealNatCode.program, RealRoundRat.program,
      RealMidpointRegister.program, RealMidpointRegister.kernel, RealMidpoint.program,
      RealRound.program, RealMidpointRegister.adapt, RealRatCode.program, htpc])
  have hm (i : ℕ) (hi : i ∈ ([20, 22, 26, 27, 40, 42, 43, 45, 46] : List ℕ)) :
      t.indices i = s.indices i := by
    have hib : 19 ≤ i ∧ i < 256 ∧ i ≠ 21 ∧ i ≠ 30 ∧ i ≠ 31 ∧ i ≠ 44 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have he := hindices i (by omega)
      (RealNatAppend.outside_metadata L' i (by omega) (by omega) (by omega))
    simpa [loaded, RAMState.setWord, RAMState.setIndex, show i ≠ 30 by omega,
      show i ≠ 31 by omega, show i ≠ 44 by omega] using he
  have hwordframe (i : ℕ) (hi : 17 ≤ i) : t.words i = s.words i := by
    simpa [loaded, RAMState.setWord, RAMState.setIndex, show i ≠ 16 by omega] using hwords i (by omega)
  have hcoordinate (i : ℕ) (hi : cb ≤ i) (hi' : i < cb + 2 * n) : t.indices i = s.indices i := by
    have he := hindices i (by omega)
      (outside_coordinate L cb n _ i hcb hcache hbuffer hi hi')
    simpa [loaded, RAMState.setWord, RAMState.setIndex, show i ≠ 30 by omega,
      show i ≠ 31 by omega, show i ≠ 44 by omega] using he
  have hprefix : StoredWord t L (word rows columns values p k) := by
    intro j hj
    have he := hindices (L.bufferAt j) (by have := L.bufferAt_ge j; omega)
      (RealNatAppend.outside_prefix L _ j hj)
    have hpref := h.stored j hj
    simpa [loaded, RAMState.setWord, RAMState.setIndex, hpref] using he
  have happend : StoredWord t L (word rows columns values p (k + 1)) :=
    RealNatCode.storedWord_append t L (word rows columns values p k)
      (RealRecordCode.word (rows k) (columns k) (values k) p) hprefix hstored
  let final := advanced {t with pc := 259}
  have hready : Ready final L rb cb n p (k + 1) rows columns values := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [final, advanced, RAMState.setIndex, hm 40 (by simp), hm 45 (by simp), h.count, h.one]
    · simp [final, advanced, RAMState.setIndex, hm 42 (by simp), hm 45 (by simp), h.realPointer, h.one, Nat.add_assoc]
    · simp [final, advanced, RAMState.setIndex, hm 43 (by simp), hm 46 (by simp), h.coordinatePointer, h.two]
      omega
    · simpa [final, advanced, RAMState.setIndex] using (hm 26 (by simp)).trans h.total
    · simpa [final, advanced, RAMState.setIndex] using (hm 27 (by simp)).trans h.precision
    · simpa [final, advanced, RAMState.setIndex] using (hm 45 (by simp)).trans h.one
    · simpa [final, advanced, RAMState.setIndex] using (hm 46 (by simp)).trans h.two
    · simpa [final, advanced, RAMState.setIndex] using (hm 20 (by simp)).trans h.cache
    · simpa [final, advanced, RAMState.setIndex, L', Layout.shiftBuffer_bufferAt, word] using hcursor
    · simpa [final, advanced, RAMState.setIndex] using (hm 22 (by simp)).trans h.stride
    · intro j hj
      exact (hwordframe (rb + j) (by omega)).trans (h.coefficients j hj)
    · intro j hj
      have hlow : ∀ i < 64, cb + 2 * j ≠ i := by omega
      have hlow' : ∀ i < 64, cb + 2 * j + 1 ≠ i := by omega
      constructor
      · simpa [final, advanced, RAMState.setIndex, hlow] using
          (hcoordinate (cb + 2 * j) (by omega) (by omega)).trans (h.coordinates j hj).1
      · simpa [final, advanced, RAMState.setIndex, hlow'] using
          (hcoordinate (cb + 2 * j + 1) (by omega) (by omega)).trans (h.coordinates j hj).2
    · intro j hj
      simpa [final, advanced, RAMState.setIndex] using happend j hj
  have hload := execute_sound _ (load_steps input tape L rb cb n p k rows columns values s hcb h hk)
  have hfinish := execute_sound _ (advance_steps input tape {t with pc := 259} rfl)
  refine ⟨5 + (cost + 1) + 4, final, by omega, (hload.trans hcall).trans hfinish, hready,
    hwordframe, ?_, ho, hio, hrandom⟩
  intro i hi hout
  have he := hindices i (by omega) (hout.shift (word rows columns values p k).length)
  simpa [final, advanced, loaded, RAMState.setWord, RAMState.setIndex,
    show i ≠ 30 by omega, show i ≠ 31 by omega, show i ≠ 44 by omega,
    show i ≠ 40 by omega, show i ≠ 42 by omega, show i ≠ 43 by omega] using he

end Maxwell.Cost.RealSparseCode
