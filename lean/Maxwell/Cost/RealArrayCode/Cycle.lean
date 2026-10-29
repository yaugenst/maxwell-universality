import Maxwell.Cost.RealArrayCode.Program

namespace Maxwell.Cost.RealArrayCode
open RealSparse (execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

theorem cycle (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hbase : 32 ≤ base) (h : Ready s L base n p k v) (hk : k < n) :
    ∃ cost : ℕ, ∃ final : RAMState,
      cost ≤ 59 * p + 167 ∧ Steps (program.next input tape) cost s final ∧
      Ready final L base n p (k + 1) v ∧ final.output = s.output ∧
      final.indexOutput = s.indexOutput ∧ final.randomCursor = s.randomCursor ∧
      (∀ i, Outside L i → final.indices i = s.indices i) := by
  let L' := L.shiftBuffer (word v p k).length
  obtain ⟨cost, t, hcost, ht, htpc, hstored, hcursor, hwords, hindices, ho, hio, hrandom⟩ :=
    RealRoundRat.terminates input tape L' {loaded s with pc := 0} (v k) p rfl
      (by simp [loaded, RAMState.setWord, h.source, h.values k hk])
      h.precision h.cache h.buffer h.stride
  have hcall := contains_round.call_at input tape (loaded s) t rfl ht.toSteps (by
    simp [RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
      RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt,
      RealRatCode.program, RealNatCode.program, htpc])
  have hm (i : ℕ) (hi : 19 ≤ i) (hi' : i < 256) (hne : i ≠ 21) : t.indices i = s.indices i :=
    hindices i hi (RealRatCode.protected_metadata L' _ _ i (by omega) hi' hne)
  have hprefix : StoredWord t L (word v p k) := by
    intro j hj
    exact (hindices (L.bufferAt j) (by have := L.bufferAt_ge j; omega)
      (protected_prefix L _ _ _ j hj)).trans (h.stored j hj)
  have happend : StoredWord t L (word v p (k + 1)) :=
    RealNatCode.storedWord_append t L (word v p k)
      (Codec.rat (RealMidpoint.approximation (v k) p)) hprefix hstored
  let final := advanced {t with pc := 168}
  have hready : Ready final L base n p (k + 1) v := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [final, advanced, RAMState.setIndex, hm 23 (by omega) (by omega) (by omega),
        hm 28 (by omega) (by omega) (by omega), h.count, h.one]
    · simp [final, advanced, RAMState.setIndex, hm 24 (by omega) (by omega) (by omega),
        hm 28 (by omega) (by omega) (by omega), h.source, h.one, Nat.add_assoc]
    · simpa [final, advanced, RAMState.setIndex] using (hm 26 (by omega) (by omega) (by omega)).trans h.total
    · simpa [final, advanced, RAMState.setIndex] using (hm 27 (by omega) (by omega) (by omega)).trans h.precision
    · simpa [final, advanced, RAMState.setIndex] using (hm 28 (by omega) (by omega) (by omega)).trans h.one
    · simpa [final, advanced, RAMState.setIndex] using (hm 20 (by omega) (by omega) (by omega)).trans h.cache
    · simpa [final, advanced, RAMState.setIndex, L', Layout.shiftBuffer_bufferAt, word] using hcursor
    · simpa [final, advanced, RAMState.setIndex] using (hm 22 (by omega) (by omega) (by omega)).trans h.stride
    · intro j hj
      have hneq : base + j ≠ 16 := by omega
      have hv := hwords (base + j) (by omega)
      simpa [final, advanced, loaded, RAMState.setIndex, RAMState.setWord, hneq, h.values j hj] using hv
    · intro j hj
      simpa [final, advanced, RAMState.setIndex] using happend j hj
  have hload := execute_sound _ (load_steps input tape L base n p k v s h hk)
  have hfinish := execute_sound _ (advance_steps input tape {t with pc := 168} rfl)
  refine ⟨2 + (cost + 1) + 3, final, by omega, (hload.trans hcall).trans hfinish,
    hready, ho, hio, hrandom, ?_⟩
  intro i hi
  have hprotected : RealRatCode.Protected L' (RealMidpoint.approximation (v k) p).num.natAbs
      (RealMidpoint.approximation (v k) p).den i := by
    refine ⟨by have := hi.1; omega, by have := hi.1; omega, fun j _ => hi.2.1 j, ?_⟩
    intro j _
    simpa [L'] using hi.2.2 ((word v p k).length + j)
  simpa [final, advanced, loaded, RAMState.setIndex, RAMState.setWord, show i ≠ 23 by have := hi.1; omega,
    show i ≠ 24 by have := hi.1; omega] using hindices i (by have := hi.1; omega) hprotected

end Maxwell.Cost.RealArrayCode
