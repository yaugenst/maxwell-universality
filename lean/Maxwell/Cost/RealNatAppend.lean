import Maxwell.Cost.RealRatCode.Program

namespace Maxwell.Cost.RealNatAppend
open RealNatCode (Layout StoredWord)
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

/-- Natural codec with a charged cursor update, suitable for repeated calls. -/
def program : Machine := ⟨
  (RealNatCode.program.code.map (RAMInstruction.relocate 0 37)) ++
  [.indexSubtract 21 6 21, .indexAdd 21 21 6, .indexAdd 21 21 22, .halt]⟩

theorem contains_nat : program.Contains RealNatCode.program 0 37 := by
  intro i; fin_cases i <;> rfl

def Outside (L : Layout) (i : ℕ) : Prop :=
  11 ≤ i ∧ i ≠ 21 ∧ (∀ j, i ≠ L.cacheAt j) ∧ ∀ j, i ≠ L.bufferAt j

theorem outside_metadata (L : Layout) (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256)
    (hne : i ≠ 21) : Outside L i := by
  refine ⟨hi, hne, ?_, ?_⟩
  · intro j; have := L.cacheAt_ge j; omega
  · intro j; have := L.bufferAt_ge j; omega

theorem outside_prefix (L : Layout) (offset j : ℕ) (hj : j < offset) :
    Outside (L.shiftBuffer offset) (L.bufferAt j) := by
  refine ⟨by have := L.bufferAt_ge j; omega, by have := L.bufferAt_ge j; omega,
    fun k => (L.disjoint k j).symm, ?_⟩
  intro k
  rw [Layout.shiftBuffer_bufferAt]
  intro he
  have := L.bufferAt_injective he
  omega

theorem Outside.shift {L : Layout} {i : ℕ} (h : Outside L i) (offset : ℕ) :
    Outside (L.shiftBuffer offset) i := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro j
  simpa using h.2.2.2 (offset + j)

theorem finish_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 37) :
    execute (program.next input tape) 3 s = some (RealRatCode.advancedCursor s) := by
  simp [execute, program, RealNatCode.program, Machine.next, hpc,
    RealRatCode.advancedCursor, RAMState.setIndex]

theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (n : ℕ)
    (s : RAMState) (hpc : s.pc = 0) (hn : s.indices 2 = n)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ t : RAMState, Terminates (program.next input tape) (23 * n.size + 17) s t ∧
      t.pc = 40 ∧ StoredWord t L (Codec.nat n) ∧
      t.indices 21 = L.bufferAt (Codec.nat n).length ∧ t.words = s.words ∧
      (∀ i, Outside L i → t.indices i = s.indices i) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor := by
  obtain ⟨r, hr, hrpc, _, hr6, hstored, hframe⟩ :=
    RealNatCode.terminates_frame input tape L n s hpc hn hc hb hstride
  have hcall := contains_nat.call input tape hr.toSteps (by simp [RealNatCode.program, hrpc])
  have hid : s.relocate 0 = s := by simp [RAMState.relocate]
  rw [hid] at hcall
  have hr21 : r.indices 21 = L.buffer :=
    (hframe.indices 21 (RealNatCode.protected_metadata L n 21 (by omega) (by omega))).trans hb
  have hr22 : r.indices 22 = L.stride :=
    (hframe.indices 22 (RealNatCode.protected_metadata L n 22 (by omega) (by omega))).trans hstride
  let t := RealRatCode.advancedCursor {r with pc := 37}
  have hfinish := execute_sound _ (finish_steps input tape {r with pc := 37} rfl)
  refine ⟨t, ?_, by simp [t], ?_, ?_, hframe.words, ?_, hframe.output, hframe.indexOutput, hframe.randomCursor⟩
  · convert (hcall.trans hfinish).terminates
      (Terminates.halt _ (by simp [program, RealNatCode.program, Machine.next,
        RealRatCode.advancedCursor, RAMState.setIndex])) using 1
  · exact RealRatCode.advancedCursor_stored L {r with pc := 37} (Codec.nat n) hstored
  · simp only [t, RealRatCode.advancedCursor, RAMState.setIndex, Function.update_apply, ↓reduceIte,
      hr6, hr21, hr22]
    rw [RealRatCode.cursor_formula, RealNatCode.code_length]
  · intro i hi
    have he := hframe.indices i ⟨hi.1, fun j _ => hi.2.2.1 j, fun j _ => hi.2.2.2 j⟩
    simpa [t, RealRatCode.advancedCursor, RAMState.setIndex, hi.2.1] using he

end Maxwell.Cost.RealNatAppend
