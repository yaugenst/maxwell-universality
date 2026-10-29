import Maxwell.Cost.RealArrayCode.Correctness

namespace Maxwell.Cost.RealVectorCode
open RealNatCode (Layout StoredWord)
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

noncomputable def values (v : ℕ → ℝ) (p n : ℕ) : List ℚ :=
  (List.range n).map (fun i => RealMidpoint.approximation (v i) p)

def program : Machine := ⟨[.indexCopy 2 26] ++
  (RealNatCode.program.code.map (RAMInstruction.relocate 1 38)) ++
  [.indexSubtract 21 6 21, .indexAdd 21 21 6, .indexAdd 21 21 22] ++
  (RealArrayCode.program.code.map (RAMInstruction.relocate 41 213)) ++ [.halt]⟩

theorem contains_count : program.Contains RealNatCode.program 1 38 := by
  intro i; fin_cases i <;> rfl

theorem contains_array : program.Contains RealArrayCode.program 41 213 := by
  intro i; fin_cases i <;> rfl

theorem start_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 1 s = some (s.setIndex 2 (s.indices 26)) := by
  simp [execute, program, Machine.next, hpc]

theorem bridge_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 38) :
    execute (program.next input tape) 3 s = some (RealRatCode.advancedCursor s) := by
  simp [execute, program, RealNatCode.program, Machine.next, hpc,
    RealRatCode.advancedCursor, RAMState.setIndex]

/-- Actual count-prefixed canonical rational encoding of the addressed real
vector. The input vector is neither copied nor rounded by the metatheory. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hs : s.indices 24 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 167) * n + 23 * n.size + 22 ∧
      Terminates (program.next input tape) cost s t ∧ t.pc = 213 ∧
      StoredWord t L (Codec.list Codec.rat (values v p n)) := by
  let a := s.setIndex 2 (s.indices 26)
  obtain ⟨r, hr, hrpc, _, hr6, hrstored, hrframe⟩ := RealNatCode.terminates_frame
    input tape L n {a with pc := 0} rfl (by simp [a, RAMState.setIndex, hn])
      (by simpa [a, RAMState.setIndex] using hc) (by simpa [a, RAMState.setIndex] using hb)
      (by simpa [a, RAMState.setIndex] using hstride)
  have hfirst := contains_count.call_at input tape a r (by simp [a, RAMState.setIndex, hpc]) hr.toSteps
    (by simp [RealNatCode.program, hrpc])
  have hm (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) : r.indices i = s.indices i := by
    have he := hrframe.indices i (RealNatCode.protected_metadata L n i hi hi')
    simpa [a, RAMState.setIndex, show i ≠ 2 by omega] using he
  let b := RealRatCode.advancedCursor {r with pc := 38}
  let L' := L.shiftBuffer (Codec.nat n).length
  have hb' : b.indices 21 = L'.buffer := by
    simp only [b, RealRatCode.advancedCursor, RAMState.setIndex, Function.update_apply, ↓reduceIte,
      hr6, hm 21 (by omega) (by omega), hm 22 (by omega) (by omega), hb, hstride]
    rw [RealRatCode.cursor_formula]
    simp [L', Layout.shiftBuffer, RealNatCode.code_length]
  have hbmeta (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) : b.indices i = s.indices i := by
    simp [b, RealRatCode.advancedCursor, RAMState.setIndex, hne, hm i hi hi']
  have hbvalues : ∀ j < n, b.words (base + j) = v j := by
    intro j hj
    exact (congrFun hrframe.words (base + j)).trans (hv j hj)
  obtain ⟨cost, t, hbound, ht, htpc, hstored, _, _, _, _, _, hframe⟩ :=
    RealArrayCode.terminates input tape L' base n p v {b with pc := 0} hbase rfl
      ((hbmeta 24 (by omega) (by omega) (by omega)).trans hs)
      ((hbmeta 26 (by omega) (by omega) (by omega)).trans hn)
      ((hbmeta 27 (by omega) (by omega) (by omega)).trans hp)
      ((hbmeta 20 (by omega) (by omega) (by omega)).trans hc) hb'
      ((hbmeta 22 (by omega) (by omega) (by omega)).trans hstride) hbvalues
  have hsecond := contains_array.call_at input tape b t (by simp [b]) ht.toSteps (by
    simp [RealArrayCode.program, RealRoundRat.program, RealMidpointRegister.program,
      RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program,
      RealMidpointRegister.adapt, RealRatCode.program, RealNatCode.program, htpc])
  have hheader : StoredWord t L (Codec.nat n) := by
    intro j hj
    have he := hframe (L.bufferAt j) (RealArrayCode.outside_prefix L _ j hj)
    have hrj := hrstored j hj
    simpa [b, RealRatCode.advancedCursor, RAMState.setIndex, hrj] using he
  have hall := RealNatCode.storedWord_append t L (Codec.nat n) (RealArrayCode.word v p n) hheader hstored
  have hstart := execute_sound _ (start_steps input tape s hpc)
  have hbridge := execute_sound _ (bridge_steps input tape {r with pc := 38} rfl)
  refine ⟨1 + (23 * n.size + 13 + 1) + 3 + (cost + 1), {t with pc := 213}, by omega,
    ?_, rfl, ?_⟩
  · exact (((hstart.trans hfirst).trans hbridge).trans hsecond).terminates
      (Terminates.halt _ (by simp [program, RealArrayCode.program, RealRoundRat.program,
        RealMidpointRegister.program, RealMidpointRegister.kernel, RealMidpoint.program,
        RealRound.program, RealMidpointRegister.adapt, RealRatCode.program, RealNatCode.program, Machine.next]))
  · simpa [StoredWord, Codec.list, values, RealArrayCode.word_eq_flatMap, List.flatMap_map] using hall

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hs : s.indices 24 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) ((59 * p + 167) * n + 23 * n.size + 23) s).finished = some t ∧
      (runCapped (program.next input tape) ((59 * p + 167) * n + 23 * n.size + 23) s).instructions ≤
        (59 * p + 167) * n + 23 * n.size + 22 ∧
      StoredWord t L (Codec.list Codec.rat (values v p n)) := by
  obtain ⟨cost, t, hbound, ht, _, hstored⟩ :=
    terminates input tape L base n p v s hbase hpc hs hn hp hc hb hstride hv
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates_ge _ ht
    ((59 * p + 167) * n + 23 * n.size + 23) (by omega)
  exact ⟨t, hf, hcost.le.trans hbound, hstored⟩

theorem rational_length_le (x : ℝ) (p : ℕ) :
    (Codec.rat (RealMidpoint.approximation x p)).length ≤ 4 * p + 9 := by
  have hn := RealMidpoint.numerator_bits_le x p
  have hd := RealMidpoint.denominator_bits_le x p
  rw [Nat.size_eq_bits_len] at hn hd
  simp only [Codec.rat, Codec.int, List.length_append, List.length_cons,
    RealNatCode.code_length]
  omega

theorem word_length_le (v : ℕ → ℝ) (p n : ℕ) :
    (RealArrayCode.word v p n).length ≤ (4 * p + 9) * n := by
  induction n with
  | zero => simp [RealArrayCode.word]
  | succ n ih =>
    rw [RealArrayCode.word, List.length_append]
    calc
      _ ≤ (4 * p + 9) * n + (4 * p + 9) := Nat.add_le_add ih (rational_length_le (v n) p)
      _ = (4 * p + 9) * (n + 1) := by ring

theorem output_length_le (v : ℕ → ℝ) (p n : ℕ) :
    (Codec.list Codec.rat (values v p n)).length ≤ 2 * n.size + 1 + (4 * p + 9) * n := by
  have h := word_length_le v p n
  simpa [Codec.list, values, RealArrayCode.word_eq_flatMap, List.flatMap_map,
    RealNatCode.code_length] using Nat.add_le_add_left h (2 * n.size + 1)

end Maxwell.Cost.RealVectorCode
