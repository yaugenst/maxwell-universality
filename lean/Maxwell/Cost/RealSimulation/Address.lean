import Maxwell.Cost.RealSimulation.ControlCorrectness

/-! A finite Real-RAM decoder for a strided bank of most-significant-first
bits. All reads, additions, tests, and backedges are actual instructions. -/
namespace Maxwell.Cost.RealSimulation.Address
open Control

def initProgram : Machine := ⟨[
  .indexLiteral 3 0, .indexLiteral 4 1, .indexCopy 5 1,
  .indexLiteral 7 1, .indexLiteral 8 0, .halt]⟩

def body : Machine := ⟨[
  .loadIndex 6 5, .indexAdd 3 3 3, .indexAdd 3 3 6,
  .indexAdd 4 4 7, .indexAdd 5 5 2, .halt]⟩

/-- Cursor 4 is one-based, so the loop's ordinary comparison is `cursor ≤ len`.
Registers 0, 1, and 2 supply length, base, and stride; register 3 is the result. -/
def code : Code := .seq (.call initProgram) (.loop 4 0 (.call body))
def program : Machine := code.compile

theorem program_length : program.code.length = 14 := by decide

structure Frame (s t : RAMState) : Prop where
  words : t.words = s.words
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  indices : ∀ i, i < 3 ∨ 8 < i → t.indices i = s.indices i

theorem Frame.refl (s : RAMState) : Frame s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {s t u : RAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.words.trans h.words, k.randomCursor.trans h.randomCursor,
    k.output.trans h.output, k.indexOutput.trans h.indexOutput,
    fun i hi => (k.indices i hi).trans (h.indices i hi)⟩

theorem Frame.setPC {s t : RAMState} (h : Frame s t) (pc : ℕ) : Frame s {t with pc := pc} :=
  ⟨h.words, h.randomCursor, h.output, h.indexOutput, h.indices⟩

def initialized (s : RAMState) : RAMState :=
  {s with
    pc := s.pc + 5
    indices := Function.update (Function.update (Function.update
      (Function.update (Function.update s.indices 3 0) 4 1) 5 (s.indices 1)) 7 1) 8 0}

def advanced (s : RAMState) : RAMState :=
  {s with
    pc := s.pc + 5
    indices := Function.update (Function.update (Function.update
      (Function.update s.indices 6 (s.indices (s.indices 5)))
      3 (2 * s.indices 3 + s.indices (s.indices 5)))
      4 (s.indices 4 + s.indices 7)) 5 (s.indices 5 + s.indices 2)}

theorem initialized_frame (s : RAMState) : Frame s (initialized s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [initialized, show i ≠ 3 by omega,
    show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega]

theorem advanced_frame (s : RAMState) : Frame s (advanced s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [advanced, show i ≠ 3 by omega,
    show i ≠ 4 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega]

theorem initialize_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call initProgram) 6 s (Store.ofState (initialized s.val)) := by
  apply Executes.call (cost := 5)
  · apply advance_steps
    simp [advance, Machine.next, initProgram, initialized, RAMState.setIndex, s.property]
  · simp [initProgram, initialized, s.property]

theorem body_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call body) 6 s (Store.ofState (advanced s.val)) := by
  apply Executes.call (cost := 5)
  · apply advance_steps
    simp [advance, Machine.next, body, advanced, RAMState.setIndex, s.property, two_mul]
  · simp [body, advanced, s.property]

private theorem fold_reverse (bits : List Bool) (acc : ℕ) :
    bits.reverse.foldl (fun a b => 2 * a + b.toNat) acc =
      2 ^ bits.length * acc + addressValue bits := by
  induction bits generalizing acc with
  | nil => simp [addressValue]
  | cons b bits ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih, List.length_cons, addressValue, pow_succ]
    ring

/-- A general remaining-bank loop invariant. The bank lies above scratch
registers, so each actual iteration preserves the remaining source bits. -/
theorem loop_executes (input : RAMInput) (tape : ℕ → Bool) (bits : List Bool)
    (offset base stride : ℕ) (hbase : 9 ≤ base) (s : Store)
    (hlen : s.val.indices 0 = offset + bits.length)
    (hcursor : s.val.indices 4 = offset + 1)
    (haddress : s.val.indices 5 = base) (hstride : s.val.indices 2 = stride)
    (hone : s.val.indices 7 = 1)
    (hbank : ∀ j (hj : j < bits.length), s.val.indices (base + stride * j) = (bits[j]'hj).toNat) :
    ∃ t : Store, Executes input tape (.loop 4 0 (.call body)) (7 * bits.length + 1) s t ∧
      t.val.indices 3 = bits.foldl (fun a b => 2 * a + b.toNat) (s.val.indices 3) ∧
      t.val.indices 4 = offset + bits.length + 1 ∧
      t.val.indices 5 = base + stride * bits.length ∧ Frame s.val t.val := by
  induction bits generalizing offset base s with
  | nil =>
    refine ⟨s, ?_, rfl, ?_, ?_, Frame.refl _⟩
    · apply Executes.done
      simp only [hlen, hcursor, List.length_nil, Nat.add_zero]
      omega
    · simpa using hcursor
    · simpa using haddress
  | cons bit bits ih =>
    have hbit : s.val.indices (s.val.indices 5) = bit.toNat := by
      have hb := hbank 0 (by simp)
      change s.val.indices (base + stride * 0) = bit.toNat at hb
      simpa only [haddress, Nat.mul_zero, Nat.add_zero] using hb
    let middle := Store.ofState (advanced s.val)
    have hm : Frame s.val middle.val := (advanced_frame s.val).setPC 0
    have hbank' : ∀ j (hj : j < bits.length),
        middle.val.indices (base + stride + stride * j) = (bits[j]'hj).toNat := by
      intro j hj
      rw [hm.indices _ (Or.inr (by omega))]
      have hb := hbank (j + 1) (by simp; omega)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
    obtain ⟨t, et, ht3, ht4, ht5, htf⟩ := ih (offset + 1) (base + stride) (by omega) middle
      (by rw [hm.indices 0 (by omega)]; simp only [List.length_cons] at hlen; omega)
      (by simp [middle, Store.ofState, advanced, hcursor, hone])
      (by simp [middle, Store.ofState, advanced, haddress, hstride])
      (by simpa only [hm.indices 2 (by omega)] using hstride)
      (by simpa [middle, Store.ofState, advanced] using hone) hbank'
    refine ⟨t, ?_, ?_, ?_, ?_, hm.trans htf⟩
    · have test : s.val.indices 4 ≤ s.val.indices 0 := by
        simp only [hcursor, hlen, List.length_cons]
        omega
      convert Executes.more test (body_executes input tape s) et using 1
      simp only [List.length_cons]
      omega
    · simpa [List.foldl_cons, middle, Store.ofState, advanced, hbit] using ht3
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht4
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht5

/-- Decode the original little-endian address from its reversed strided bank.
The exact finite execution costs seven operations per bit plus seven. -/
theorem executes (input : RAMInput) (tape : ℕ → Bool) (bits : List Bool)
    (base stride : ℕ) (hbase : 9 ≤ base) (s : Store)
    (hlen : s.val.indices 0 = bits.length) (hbaseWord : s.val.indices 1 = base)
    (hstride : s.val.indices 2 = stride)
    (hbank : ∀ j < bits.length,
      s.val.indices (base + stride * j) = (bits.reverse[j]?.getD false).toNat) :
    ∃ t : Store, Executes input tape code (7 * (bits.length + 1)) s t ∧
      t.val.indices 3 = addressValue bits ∧ t.val.indices 4 = bits.length + 1 ∧
      t.val.indices 5 = base + stride * bits.length ∧ Frame s.val t.val := by
  let middle := Store.ofState (initialized s.val)
  have hm : Frame s.val middle.val := (initialized_frame s.val).setPC 0
  have hbank' : ∀ j (hj : j < bits.reverse.length),
      middle.val.indices (base + stride * j) = (bits.reverse[j]'hj).toNat := by
    intro j hj
    rw [hm.indices _ (Or.inr (by omega))]
    simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using hbank j (by simpa using hj)
  obtain ⟨t, et, ht3, ht4, ht5, htf⟩ := loop_executes input tape bits.reverse 0 base stride hbase middle
    (by simpa only [hm.indices 0 (by omega), List.length_reverse, Nat.zero_add] using hlen)
    (by simp [middle, Store.ofState, initialized])
    (by simp [middle, Store.ofState, initialized, hbaseWord])
    (by simpa only [hm.indices 2 (by omega)] using hstride)
    (by simp [middle, Store.ofState, initialized]) hbank'
  refine ⟨t, ?_, ?_, ?_, ?_, hm.trans htf⟩
  · have et' : Executes input tape (.loop 4 0 (.call body)) (7 * bits.length + 1) middle t :=
      by simpa only [List.length_reverse] using et
    rw [show 7 * (bits.length + 1) = 6 + (7 * bits.length + 1) by omega]
    exact (initialize_executes input tape s).seq et'
  · rw [fold_reverse] at ht3
    simpa [middle, Store.ofState, initialized] using ht3
  · simpa only [List.length_reverse, Nat.zero_add] using ht4
  · simpa only [List.length_reverse] using ht5

theorem simulation (input : RAMInput) (tape : ℕ → Bool) (bits : List Bool)
    (base stride : ℕ) (hbase : 9 ≤ base) (s : RAMState) (hpc : s.pc = 0)
    (hlen : s.indices 0 = bits.length) (hbaseWord : s.indices 1 = base)
    (hstride : s.indices 2 = stride)
    (hbank : ∀ j < bits.length,
      s.indices (base + stride * j) = (bits.reverse[j]?.getD false).toNat) :
    ∃ t, Steps (program.next input tape) (7 * (bits.length + 1)) s t ∧
      program.code[t.pc]? = some .halt ∧ t.indices 3 = addressValue bits ∧
      t.indices 4 = bits.length + 1 ∧ t.indices 5 = base + stride * bits.length ∧ Frame s t := by
  obtain ⟨t, et, ht3, ht4, ht5, hf⟩ := executes input tape bits base stride hbase
    ⟨s, hpc⟩ hlen hbaseWord hstride hbank
  exact ⟨t.place code.size, et.compiled_steps, code.compile_halt, ht3, ht4, ht5, hf.setPC _⟩

/-- A uniform linear cap observes the actual halt and preserves every
non-scratch cell, including the source bank. -/
theorem run (input : RAMInput) (tape : ℕ → Bool) (bits : List Bool)
    (base stride : ℕ) (hbase : 9 ≤ base) (s : RAMState) (hpc : s.pc = 0)
    (hlen : s.indices 0 = bits.length) (hbaseWord : s.indices 1 = base)
    (hstride : s.indices 2 = stride)
    (hbank : ∀ j < bits.length,
      s.indices (base + stride * j) = (bits.reverse[j]?.getD false).toNat) :
    ∃ t, (runCapped (program.next input tape) (10 * (bits.length + 1) + 1) s).finished = some t ∧
      (runCapped (program.next input tape) (10 * (bits.length + 1) + 1) s).instructions ≤
        10 * (bits.length + 1) ∧
      t.indices 3 = addressValue bits ∧ t.indices 4 = bits.length + 1 ∧
      t.indices 5 = base + stride * bits.length ∧ Frame s t := by
  obtain ⟨t, et, ht3, ht4, ht5, hf⟩ := executes input tape bits base stride hbase
    ⟨s, hpc⟩ hlen hbaseWord hstride hbank
  have hr := et.compiled_run (10 * (bits.length + 1) + 1) (by omega)
  refine ⟨t.place code.size, hr.1, ?_, ht3, ht4, ht5, hf.setPC _⟩
  change (runCapped (code.compile.next input tape) _ s).instructions ≤ _
  rw [hr.2]
  omega

end Maxwell.Cost.RealSimulation.Address
