import Maxwell.Cost.RealRatCode.Program

namespace Maxwell.Cost.RealRatCode
open RealNatCode (Layout StoredWord)

/-- The rational writer changes its low scratch registers, its cursor, its
power cache, and exactly the newly allocated codec interval. -/
def Protected (L : Layout) (num den i : ℕ) : Prop :=
  11 ≤ i ∧ i ≠ 21 ∧
    (∀ j < max num.size den.size, i ≠ L.cacheAt j) ∧
    ∀ j < 1 + (Codec.nat num).length + (Codec.nat den).length, i ≠ L.bufferAt j

structure Frame (L : Layout) (num den : ℕ) (s t : RAMState) : Prop where
  words : t.words = s.words
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  indices : ∀ i, Protected L num den i → t.indices i = s.indices i

theorem Protected.numerator {L : Layout} {num den i : ℕ} (h : Protected L num den i) :
    RealNatCode.Protected (L.shiftBuffer 1) num i := by
  refine ⟨h.1, fun j hj => h.2.2.1 j (lt_of_lt_of_le hj (le_max_left _ _)), ?_⟩
  intro j hj
  rw [Layout.shiftBuffer_bufferAt]
  apply h.2.2.2
  rw [RealNatCode.code_length, RealNatCode.code_length]
  omega

theorem Protected.denominator {L : Layout} {num den i : ℕ} (h : Protected L num den i) :
    RealNatCode.Protected (L.shiftBuffer (1 + (Codec.nat num).length)) den i := by
  refine ⟨h.1, fun j hj => h.2.2.1 j (lt_of_lt_of_le hj (le_max_right _ _)), ?_⟩
  intro j hj
  rw [Layout.shiftBuffer_bufferAt]
  apply h.2.2.2
  rw [RealNatCode.code_length, RealNatCode.code_length]
  omega

theorem started_frame (L : Layout) (num den : ℕ) (s : RAMState)
    (hb : s.indices 21 = L.buffer) : Frame L num den s (started s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have h2 : i ≠ 2 := by have := hi.1; omega
  have hbuf : i ≠ L.buffer := by
    simpa [Layout.bufferAt] using hi.2.2.2 0 (by omega)
  simp [started, RAMState.setIndex, hb, h2, hi.2.1, hbuf]

theorem advancedCursor_frame (L : Layout) (num den : ℕ) (s : RAMState) :
    Frame L num den s (advancedCursor s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [advancedCursor, RAMState.setIndex, hi.2.1]

theorem denominatorStart_frame (L : Layout) (num den : ℕ) (s : RAMState) :
    Frame L num den s (denominatorStart s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have h2 : i ≠ 2 := by have := hi.1; omega
  simp [denominatorStart, advancedCursor, RAMState.setIndex, h2, hi.2.1]

theorem protected_metadata (L : Layout) (num den i : ℕ)
    (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) : Protected L num den i := by
  refine ⟨hi, hne, ?_, ?_⟩
  · intro j _; have := L.cacheAt_ge j; omega
  · intro j _; have := L.bufferAt_ge j; omega

theorem Frame.preserves_prefix {L : Layout} {offset num den : ℕ} {s t : RAMState}
    (h : Frame (L.shiftBuffer offset) num den s t) (bits : List Bool)
    (hlen : bits.length ≤ offset) (hs : StoredWord s L bits) : StoredWord t L bits := by
  intro j hj
  apply Eq.trans (h.indices (L.bufferAt j) ?_) (hs j hj)
  refine ⟨by have := L.bufferAt_ge j; omega, by have := L.bufferAt_ge j; omega, ?_, ?_⟩
  · intro k _; exact (L.disjoint k j).symm
  · intro k _
    rw [Layout.shiftBuffer_bufferAt]
    intro he
    have := L.bufferAt_injective he
    omega

end Maxwell.Cost.RealRatCode
