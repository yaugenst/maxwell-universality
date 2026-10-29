import Maxwell.Cost.RealRatCode.Frame

namespace Maxwell.Cost.RealRatCode
open RealSparse (execute execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

theorem terminates_frame (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (negative : Bool) (num den : ℕ) (s : RAMState) (hpc : s.pc = 0)
    (hn : s.indices 16 = num) (hd : s.indices 17 = den)
    (hsign : s.indices 18 = negative.toNat) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride) :
    ∃ t : RAMState,
      Terminates (program.next input tape) (23 * (num.size + den.size) + 38) s t ∧
      t.pc = 84 ∧ StoredWord t L (word negative num den) ∧
      t.indices 21 = L.bufferAt (word negative num den).length ∧ Frame L num den s t := by
  let L₁ := L.shiftBuffer 1
  let L₂ := L.shiftBuffer (1 + (Codec.nat num).length)
  let a := started s
  have hsafe : ∀ i < 256, i ≠ L.buffer := by intro i hi; have := L.buffer_ge; omega
  have ha2 : a.indices 2 = num := by simp [a, started, RAMState.setIndex, hn]
  have ha20 : a.indices 20 = L₁.cache := by simp [a, started, RAMState.setIndex, hb, hc, hsafe, L₁, Layout.shiftBuffer]
  have ha21 : a.indices 21 = L₁.buffer := by
    simp [a, started, RAMState.setIndex, hb, hstride, L₁, Layout.shiftBuffer, Layout.bufferAt]
  have ha22 : a.indices 22 = L₁.stride := by simp [a, started, RAMState.setIndex, hb, hstride, hsafe, L₁, Layout.shiftBuffer]
  have ha17 : a.indices 17 = den := by simp [a, started, RAMState.setIndex, hb, hd, hsafe]
  obtain ⟨t₁, ht₁, hp₁, _, hcursor₁, hstored₁, hframe₁⟩ := RealNatCode.terminates_frame
    input tape L₁ num {a with pc := 0} rfl ha2 ha20 ha21 ha22
  have hfirst := contains_numerator.call_at input tape a t₁ (by simp [a, hpc]) ht₁.toSteps
    (by simp [RealNatCode.program, hp₁])
  have hm₁ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) : t₁.indices i = a.indices i :=
    hframe₁.indices i (RealNatCode.protected_metadata L₁ num i hi hi')
  have ht20 : t₁.indices 20 = L.cache := (hm₁ 20 (by omega) (by omega)).trans ha20
  have ht21 : t₁.indices 21 = L₁.buffer := (hm₁ 21 (by omega) (by omega)).trans ha21
  have ht22 : t₁.indices 22 = L.stride := (hm₁ 22 (by omega) (by omega)).trans ha22
  have ht17 : t₁.indices 17 = den := (hm₁ 17 (by omega) (by omega)).trans ha17
  let b := denominatorStart {t₁ with pc := 40}
  have hb2 : b.indices 2 = den := by simp [b, denominatorStart, RAMState.setIndex, ht17]
  have hb20 : b.indices 20 = L₂.cache := by
    simp [b, denominatorStart, advancedCursor, RAMState.setIndex, ht20, L₂, Layout.shiftBuffer]
  have hb22 : b.indices 22 = L₂.stride := by
    simp [b, denominatorStart, advancedCursor, RAMState.setIndex, ht22, L₂, Layout.shiftBuffer]
  have hb21 : b.indices 21 = L₂.buffer := by
    simp only [b, denominatorStart, advancedCursor, RAMState.setIndex, Function.update_apply,
      Nat.reduceEqDiff, ↓reduceIte, ht21, ht22, hcursor₁]
    change L₁.bufferAt num.size - L₁.buffer + L₁.bufferAt num.size + L₁.stride = _
    rw [cursor_formula]
    simp [L₁, L₂, Layout.shiftBuffer, Layout.bufferAt, RealNatCode.code_length, Nat.mul_add, Nat.add_assoc]
  obtain ⟨t₂, ht₂, hp₂, _, hcursor₂, hstored₂, hframe₂⟩ := RealNatCode.terminates_frame
    input tape L₂ den {b with pc := 0} rfl hb2 hb20 hb21 hb22
  have hsecond := contains_denominator.call_at input tape b t₂ (by simp [b]) ht₂.toSteps
    (by simp [RealNatCode.program, hp₂])
  have hsign : StoredWord t₁ L [negative] := hframe₁.preserves_prefix [negative] (by simp)
    (started_sign L s negative hb hsign)
  let left := [negative] ++ Codec.nat num
  have hleft₁ : StoredWord t₁ L left :=
    RealNatCode.storedWord_append t₁ L [negative] (Codec.nat num) hsign hstored₁
  have hleftb : StoredWord b L left := denominatorStart_stored L {t₁ with pc := 40} left hleft₁
  have hleft₂ : StoredWord t₂ L left := hframe₂.preserves_prefix left (by simp [left]) hleftb
  have hwhole : StoredWord t₂ L (word negative num den) := by
    have hr : StoredWord t₂ (L.shiftBuffer left.length) (Codec.nat den) := by
      change StoredWord t₂ L₂ (Codec.nat den) at hstored₂
      simpa [L₂, left, Nat.add_comm] using hstored₂
    simpa [left, word] using RealNatCode.storedWord_append t₂ L left (Codec.nat den) hleft₂ hr
  let t := advancedCursor {t₂ with pc := 81}
  have hm₂ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) : t₂.indices i = b.indices i :=
    hframe₂.indices i (RealNatCode.protected_metadata L₂ den i hi hi')
  have ht21' : t₂.indices 21 = L₂.buffer := (hm₂ 21 (by omega) (by omega)).trans hb21
  have ht22' : t₂.indices 22 = L₂.stride := (hm₂ 22 (by omega) (by omega)).trans hb22
  have hend : t.indices 21 = L.bufferAt (word negative num den).length := by
    simp only [t, advancedCursor, RAMState.setIndex, Function.update_apply, ↓reduceIte, ht21', ht22', hcursor₂]
    rw [cursor_formula]
    simp [L₂, word, Layout.shiftBuffer, Layout.bufferAt, RealNatCode.code_length, Nat.mul_add, Nat.add_assoc]
    ring
  have hstart := execute_sound _ (start_steps input tape L s hpc hb)
  have hbridge := execute_sound _ (bridge_steps input tape {t₁ with pc := 40} rfl)
  have hfooter := execute_sound _ (footer_steps input tape {t₂ with pc := 81} rfl)
  have hframe : Frame L num den s t := by
    have hstartF := started_frame L num den s hb
    have hbridgeF := denominatorStart_frame L num den {t₁ with pc := 40}
    have hfinishF := advancedCursor_frame L num den {t₂ with pc := 81}
    refine ⟨hfinishF.words.trans (hframe₂.words.trans (hbridgeF.words.trans
        (hframe₁.words.trans hstartF.words))),
      hfinishF.randomCursor.trans (hframe₂.randomCursor.trans (hbridgeF.randomCursor.trans
        (hframe₁.randomCursor.trans hstartF.randomCursor))),
      hfinishF.output.trans (hframe₂.output.trans (hbridgeF.output.trans
        (hframe₁.output.trans hstartF.output))),
      hfinishF.indexOutput.trans (hframe₂.indexOutput.trans (hbridgeF.indexOutput.trans
        (hframe₁.indexOutput.trans hstartF.indexOutput))), ?_⟩
    intro i hi
    exact (hfinishF.indices i hi).trans ((hframe₂.indices i hi.denominator).trans
      ((hbridgeF.indices i hi).trans ((hframe₁.indices i hi.numerator).trans (hstartF.indices i hi))))
  refine ⟨t, ?_, by simp [t], advancedCursor_stored L {t₂ with pc := 81} _ hwhole, hend, hframe⟩
  convert ((((hstart.trans hfirst).trans hbridge).trans hsecond).trans hfooter).terminates
    (Terminates.halt t (by simp [t, program, RealNatCode.program, Machine.next, advancedCursor, RAMState.setIndex])) using 1
  omega

/-- A canonical rational is serialized from its actual sign, numerator and
denominator registers; no arithmetic conversion is performed by the theorem. -/
theorem canonical_terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (q : ℚ) (s : RAMState) (hpc : s.pc = 0)
    (hn : s.indices 16 = q.num.natAbs) (hd : s.indices 17 = q.den)
    (hsign : s.indices 18 = (decide (q.num < 0)).toNat)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ t : RAMState,
      Terminates (program.next input tape) (23 * (q.num.natAbs.size + q.den.size) + 38) s t ∧
      t.pc = 84 ∧ StoredWord t L (Codec.rat q) ∧
      t.indices 21 = L.bufferAt (Codec.rat q).length ∧ Frame L q.num.natAbs q.den s t := by
  simpa [word, Codec.rat, Codec.int] using
    terminates_frame input tape L (decide (q.num < 0)) q.num.natAbs q.den s hpc hn hd hsign hc hb hstride

theorem canonical_run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (q : ℚ) (s : RAMState) (hpc : s.pc = 0)
    (hn : s.indices 16 = q.num.natAbs) (hd : s.indices 17 = q.den)
    (hsign : s.indices 18 = (decide (q.num < 0)).toNat)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (23 * (q.num.natAbs.size + q.den.size) + 39) s).finished = some t ∧
      (runCapped (program.next input tape) (23 * (q.num.natAbs.size + q.den.size) + 39) s).instructions =
        23 * (q.num.natAbs.size + q.den.size) + 38 ∧
      StoredWord t L (Codec.rat q) ∧ t.indices 21 = L.bufferAt (Codec.rat q).length ∧
      Frame L q.num.natAbs q.den s t := by
  obtain ⟨t, ht, _, hstored, hcursor, hframe⟩ :=
    canonical_terminates input tape L q s hpc hn hd hsign hc hb hstride
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates _ ht
  exact ⟨t, hf, hcost, hstored, hcursor, hframe⟩

end Maxwell.Cost.RealRatCode
