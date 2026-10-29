import Maxwell.Cost.RealNatAppend
import Maxwell.Cost.RealRoundRat

namespace Maxwell.Cost.RealRecordCode
open RealNatCode (Layout StoredWord)
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

noncomputable def word (row column : ℕ) (x : ℝ) (p : ℕ) : List Bool :=
  Codec.nat row ++ Codec.nat column ++ Codec.rat (RealMidpoint.approximation x p)

/-- Runtime row/column labels in indices30/31 and real coefficient16 are
serialized directly in the canonical source-entry order. -/
def program : Machine := ⟨[.indexCopy 2 30] ++
  (RealNatAppend.program.code.map (RAMInstruction.relocate 1 42)) ++ [.indexCopy 2 31] ++
  (RealNatAppend.program.code.map (RAMInstruction.relocate 43 84)) ++
  (RealRoundRat.program.code.map (RAMInstruction.relocate 84 248)) ++ [.halt]⟩

theorem contains_row : program.Contains RealNatAppend.program 1 42 := by
  intro i; fin_cases i <;> rfl
theorem contains_column : program.Contains RealNatAppend.program 43 84 := by
  intro i; fin_cases i <;> rfl
theorem contains_value : program.Contains RealRoundRat.program 84 248 := by
  intro i; fin_cases i <;> rfl

theorem row_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 1 s = some (s.setIndex 2 (s.indices 30)) := by
  simp [execute, program, Machine.next, hpc]

theorem column_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 42) :
    execute (program.next input tape) 1 s = some (s.setIndex 2 (s.indices 31)) := by
  simp [execute, program, RealNatAppend.program, RealNatCode.program, Machine.next, hpc]

theorem terminates (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (row column : ℕ) (x : ℝ) (p : ℕ) (s : RAMState) (hpc : s.pc = 0)
    (hrow : s.indices 30 = row) (hcol : s.indices 31 = column)
    (hx : s.words 16 = x) (hp : s.indices 27 = p)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer)
    (hstride : s.indices 22 = L.stride) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ 59 * p + 200 + 23 * (row.size + column.size) ∧
      Terminates (program.next input tape) cost s t ∧ t.pc = 248 ∧
      StoredWord t L (word row column x p) ∧ t.indices 21 = L.bufferAt (word row column x p).length ∧
      (∀ i, 8 ≤ i → t.words i = s.words i) ∧
      (∀ i, 19 ≤ i → RealNatAppend.Outside L i → t.indices i = s.indices i) ∧
      t.output = s.output ∧ t.indexOutput = s.indexOutput ∧ t.randomCursor = s.randomCursor := by
  let a := s.setIndex 2 (s.indices 30)
  let L₁ := L.shiftBuffer (Codec.nat row).length
  let L₂ := L.shiftBuffer ((Codec.nat row).length + (Codec.nat column).length)
  obtain ⟨r₁, hr₁, hpc₁, hstored₁, hcursor₁, hw₁, hf₁, ho₁, hio₁, hrandom₁⟩ :=
    RealNatAppend.terminates input tape L row {a with pc := 0} rfl
      (by simp [a, RAMState.setIndex, hrow])
      (by simpa [a, RAMState.setIndex] using hc) (by simpa [a, RAMState.setIndex] using hb)
      (by simpa [a, RAMState.setIndex] using hstride)
  have hcall₁ := contains_row.call_at input tape a r₁ (by simp [a, RAMState.setIndex, hpc]) hr₁.toSteps
    (by simp [RealNatAppend.program, RealNatCode.program, hpc₁])
  have hm₁ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) : r₁.indices i = s.indices i := by
    simpa [a, RAMState.setIndex, show i ≠ 2 by omega] using
      hf₁ i (RealNatAppend.outside_metadata L i hi hi' hne)
  let b := ({r₁ with pc := 42} : RAMState).setIndex 2 (r₁.indices 31)
  obtain ⟨r₂, hr₂, hpc₂, hstored₂, hcursor₂, hw₂, hf₂, ho₂, hio₂, hrandom₂⟩ :=
    RealNatAppend.terminates input tape L₁ column {b with pc := 0} rfl
      (by simp [b, RAMState.setIndex, hm₁ 31 (by omega) (by omega) (by omega), hcol])
      (by simpa [b, RAMState.setIndex, L₁, Layout.shiftBuffer] using (hm₁ 20 (by omega) (by omega) (by omega)).trans hc)
      (by simpa [b, RAMState.setIndex, L₁, Layout.shiftBuffer] using hcursor₁)
      (by simpa [b, RAMState.setIndex, L₁, Layout.shiftBuffer] using (hm₁ 22 (by omega) (by omega) (by omega)).trans hstride)
  have hcall₂ := contains_column.call_at input tape b r₂ (by simp [b, RAMState.setIndex]) hr₂.toSteps
    (by simp [RealNatAppend.program, RealNatCode.program, hpc₂])
  have hm₂ (i : ℕ) (hi : 11 ≤ i) (hi' : i < 256) (hne : i ≠ 21) : r₂.indices i = s.indices i := by
    have he := hf₂ i (RealNatAppend.outside_metadata L₁ i hi hi' hne)
    simpa [b, RAMState.setIndex, show i ≠ 2 by omega, hm₁ i hi hi' hne] using he
  have hw₂' : r₂.words = s.words := hw₂.trans hw₁
  have hcursor₂' : r₂.indices 21 = L₂.buffer := by
    simpa [L₁, L₂, Layout.shiftBuffer, Layout.bufferAt, Nat.mul_add, Nat.add_assoc] using hcursor₂
  obtain ⟨cost, t, hbound, ht, htpc, hstored, hcursor, hwords, hindices, ho, hio, hrandom⟩ :=
    RealRoundRat.terminates input tape L₂ {r₂ with pc := 0} x p rfl
      ((congrFun hw₂' 16).trans hx) ((hm₂ 27 (by omega) (by omega) (by omega)).trans hp)
      ((hm₂ 20 (by omega) (by omega) (by omega)).trans hc) hcursor₂'
      ((hm₂ 22 (by omega) (by omega) (by omega)).trans hstride)
  have hcall₃ := contains_value.call_at input tape {r₂ with pc := 84} t rfl ht.toSteps
    (by simp [RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
      RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt,
      RealRatCode.program, RealNatCode.program, htpc])
  have hrow₂ : StoredWord r₂ L (Codec.nat row) := by
    intro j hj
    have he := hf₂ (L.bufferAt j) (RealNatAppend.outside_prefix L _ j hj)
    simpa [b, RAMState.setIndex, hstored₁ j hj] using he
  have hpair := RealNatCode.storedWord_append r₂ L (Codec.nat row) (Codec.nat column) hrow₂ hstored₂
  have hpair' : StoredWord t L (Codec.nat row ++ Codec.nat column) := by
    intro j hj
    have hj' : j < (Codec.nat row).length + (Codec.nat column).length := by simpa using hj
    have hh := RealNatAppend.outside_prefix L _ j hj'
    have he := hindices (L.bufferAt j) (by have := L.bufferAt_ge j; omega)
      ⟨hh.1, hh.2.1, fun k _ => hh.2.2.1 k, fun k _ => hh.2.2.2 k⟩
    exact he.trans (hpair j hj)
  have hall := RealNatCode.storedWord_append t L (Codec.nat row ++ Codec.nat column)
    (Codec.rat (RealMidpoint.approximation x p)) hpair' (by simpa [L₂] using hstored)
  have hstart := execute_sound _ (row_steps input tape s hpc)
  have hbridge := execute_sound _ (column_steps input tape {r₁ with pc := 42} rfl)
  refine ⟨1 + (23 * row.size + 17 + 1) + 1 + (23 * column.size + 17 + 1) + (cost + 1),
    {t with pc := 248}, by omega, ?_, rfl, hall, ?_, ?_, ?_,
    ho.trans (ho₂.trans ho₁), hio.trans (hio₂.trans hio₁), hrandom.trans (hrandom₂.trans hrandom₁)⟩
  · exact ((((hstart.trans hcall₁).trans hbridge).trans hcall₂).trans hcall₃).terminates
      (Terminates.halt _ (by simp [program, RealNatAppend.program, RealNatCode.program,
        RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
        RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt, RealRatCode.program, Machine.next]))
  · simpa [L₂, word, Layout.shiftBuffer_bufferAt, Nat.add_assoc] using hcursor
  · intro i hi
    exact (hwords i hi).trans (congrFun hw₂' i)
  · intro i hi hout
    have h₂ := hout.shift ((Codec.nat row).length + (Codec.nat column).length)
    have he := hindices i hi ⟨h₂.1, h₂.2.1, fun j _ => h₂.2.2.1 j, fun j _ => h₂.2.2.2 j⟩
    have he₂ := hf₂ i (hout.shift (Codec.nat row).length)
    have he₁ := hf₁ i hout
    have he₂' : r₂.indices i = r₁.indices i := by
      simpa [b, RAMState.setIndex, show i ≠ 2 by omega] using he₂
    have he₁' : r₁.indices i = s.indices i := by
      simpa [a, RAMState.setIndex, show i ≠ 2 by omega] using he₁
    exact he.trans (he₂'.trans he₁')

end Maxwell.Cost.RealRecordCode
