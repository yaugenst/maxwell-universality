import Maxwell.Cost.RealMidpointRegister.Correctness
import Maxwell.Cost.RealRatCode.Correctness

namespace Maxwell.Cost.RealRoundRat
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

/-- One finite routine rounds a real register and emits its canonical
rational codec to the caller's index-memory buffer. -/
def program : Machine := ⟨
  (RealMidpointRegister.program.code.map (RAMInstruction.relocate 0 78)) ++
  (RealRatCode.program.code.map (RAMInstruction.relocate 78 163)) ++ [.halt]⟩

theorem contains_round : program.Contains RealMidpointRegister.program 0 78 := by
  intro i
  fin_cases i <;> rfl

theorem contains_rat : program.Contains RealRatCode.program 78 163 := by
  intro i
  fin_cases i <;> rfl

/-- Every input-dependent arithmetic, sign decision, digit and buffer
write is part of the finite execution certified here. -/
theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (s : RAMState) (x : ℝ) (p : ℕ) (hpc : s.pc = 0)
    (hx : s.words 16 = x) (hp : s.indices 27 = p)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ 59 * p + 161 ∧ Terminates (program.next input tape) cost s t ∧
      t.pc = 163 ∧ StoredWord t L (Codec.rat (RealMidpoint.approximation x p)) ∧
      t.indices 21 = L.bufferAt (Codec.rat (RealMidpoint.approximation x p)).length ∧
      (∀ i, 8 ≤ i → t.words i = s.words i) ∧
      (∀ i, 19 ≤ i → RealRatCode.Protected L (RealMidpoint.approximation x p).num.natAbs
        (RealMidpoint.approximation x p).den i → t.indices i = s.indices i) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor := by
  obtain ⟨cost, r, hrbound, hr, hrpc, _, hrnum, hrden, hrsign, hrwords, hrindices, hro, hrio, hrr⟩ :=
    RealMidpointRegister.terminates input tape s x p hpc hx hp
  have hcall₁ := contains_round.call input tape hr.toSteps (by
    simp [RealMidpointRegister.program, hrpc, RealMidpointRegister.kernel,
      RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt])
  have hstart : s.relocate 0 = s := by simp [RAMState.relocate]
  rw [hstart] at hcall₁
  have hc' : r.indices 20 = L.cache := (hrindices 20 (by omega) (by omega) (by omega) (by omega)).trans hc
  have hb' : r.indices 21 = L.buffer := (hrindices 21 (by omega) (by omega) (by omega) (by omega)).trans hb
  have hs' : r.indices 22 = L.stride := (hrindices 22 (by omega) (by omega) (by omega) (by omega)).trans hstride
  obtain ⟨t, ht, htpc, hstored, hcursor, hframe⟩ := RealRatCode.canonical_terminates
    input tape L (RealMidpoint.approximation x p) {r with pc := 0} rfl hrnum hrden hrsign hc' hb' hs'
  have hcall₂ := contains_rat.call_at input tape {r with pc := 78} t rfl ht.toSteps (by
    simp [RealRatCode.program, RealNatCode.program, htpc])
  refine ⟨(cost + 1) + (23 * ((RealMidpoint.approximation x p).num.natAbs.size +
      (RealMidpoint.approximation x p).den.size) + 38 + 1), {t with pc := 163}, ?_, ?_, rfl,
    hstored, hcursor, ?_, ?_, hframe.output.trans hro, hframe.indexOutput.trans hrio,
    hframe.randomCursor.trans hrr⟩
  · have hn := RealMidpoint.numerator_bits_le x p
    have hd := RealMidpoint.denominator_bits_le x p
    rw [Nat.size_eq_bits_len] at hn hd
    omega
  · exact (hcall₁.trans hcall₂).terminates
      (Terminates.halt _ (by
        simp [program, RealMidpointRegister.program, RealRatCode.program,
          RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program,
          RealNatCode.program, Machine.next]))
  · intro i hi
    exact (congrFun hframe.words i).trans (hrwords i hi)
  · intro i hi hprotected
    exact (hframe.indices i hprotected).trans
      (hrindices i (by omega) (by omega) (by omega) (by omega))

theorem run (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (s : RAMState) (x : ℝ) (p : ℕ) (hpc : s.pc = 0)
    (hx : s.words 16 = x) (hp : s.indices 27 = p)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ t : RAMState,
      (runCapped (program.next input tape) (59 * p + 162) s).finished = some t ∧
      (runCapped (program.next input tape) (59 * p + 162) s).instructions ≤ 59 * p + 161 ∧
      StoredWord t L (Codec.rat (RealMidpoint.approximation x p)) := by
  obtain ⟨cost, t, hbound, ht, _, hstored, _⟩ := terminates input tape L s x p hpc hx hp hc hb hstride
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates_ge _ ht (59 * p + 162) (by omega)
  exact ⟨t, hf, hcost.le.trans hbound, hstored⟩

end Maxwell.Cost.RealRoundRat
