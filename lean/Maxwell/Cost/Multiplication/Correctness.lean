import Maxwell.Cost.Multiplication.Loop
import Maxwell.Cost.Multiplication.AddCycle

namespace Maxwell.Cost.HornerMultiply

/-- Uniform correctness of the outer Horner loop. The bound applies to the
actual linked Boolean program, including every tape traverse and return. -/
theorem loop_simulation_full (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (hxs : 0 < xs.length) (remaining acc : List Bool) (B : ℕ)
    (s : BitRAMState) (ao xo zo yo : ℤ)
    (hxB : xs.length ≤ B) (haB : acc.length ≤ B)
    (hpc : s.pc = 2) (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : PrefixTape (s.tapes 3) remaining yo) :
    ∃ cost t resultOrigin scratchOrigin,
      cost ≤ 200 * (B + 2 * remaining.length + 4) * remaining.length + 4 ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 71 ∧
      t.tapes 0 = BitTape.shifted (multiplyFrom xs acc remaining) resultOrigin ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 3 = {s.tapes 3 with head := yo - 1} := by
  induction remaining using List.reverseRecOn generalizing acc B s ao zo with
  | nil =>
    refine ⟨4, stoppedState s, ao, zo, by simp, stop_block input tape s hpc h3.nil_read,
      rfl, ?_, ?_, ?_, ?_⟩
    · simpa [stoppedState] using h0
    · simpa [stoppedState] using h1
    · simpa [stoppedState] using h2
    · simp [stoppedState, h3.head]
  | append_singleton remaining b ih =>
    have hshift := shift_block input tape s b hpc h3.last_read
    have hshift0 := shiftedState_accumulator s b acc ao h0
    have hshift3 := shiftedState_prefix s remaining yo b h3
    cases b with
    | false =>
      obtain ⟨cost, t, ro, so, hc, hs, hp, ht0, ht1, ht2, ht3⟩ :=
        ih (false :: acc) (B + 2) (shiftedState s false) (ao - 1) zo
          (by omega) (by simp; omega) rfl hshift0
          (by simpa [shiftedState] using h1)
          (by simpa [shiftedState] using h2) hshift3
      refine ⟨8 + cost, t, ro, so, ?_, hshift.trans hs, hp, ?_, ht1, ht2, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        nlinarith
      · simpa [multiplyFrom_append_bit, multiplyStep] using ht0
      · simpa [shiftedState] using ht3
    | true =>
      let ready := (shiftedState s true).setRegister 2 false
      have hready : PricedSteps (program.next input tape) 1 (shiftedState s true) ready := by
        apply PricedSteps.step (rest := PricedSteps.refl ready)
        simp [program, BitRAM.next, shiftedState, ready]
      obtain ⟨addCost, added, haCost, haSteps, haPc, ha0, ha1, ha2, haFrame⟩ :=
        addCycle input tape ready (false :: acc) xs (ao - 1) xo zo (by simp) hxs
          (by simp [ready, shiftedState]) (by simp [ready])
          (by simpa [ready] using hshift0)
          (by simpa [ready, shiftedState] using h1)
          (by simpa [ready, shiftedState] using h2)
      have haWidth : (addBits false (false :: acc) xs).length ≤ B + 2 := by
        simpa [multiplyStep] using multiplyStep_length_le xs acc true B hxB haB
      have haPrefix : PrefixTape (added.tapes 3) remaining yo := by
        rcases haFrame with ⟨_, _, _, _, _, ht, _⟩
        rw [ht 3 (by omega)]
        simpa [ready] using hshift3
      obtain ⟨cost, t, ro, so, hc, hs, hp, ht0, ht1, ht2, ht3⟩ :=
        ih (addBits false (false :: acc) xs) (B + 2) added
          (ao - 1 + (false :: acc).length) (zo + (addBits false (false :: acc) xs).length)
          (by omega) haWidth haPc ha0 ha1 ha2 haPrefix
      refine ⟨8 + 1 + addCost + cost, t, ro, so, ?_,
        ((hshift.trans hready).trans haSteps).trans hs, hp, ?_, ht1, ht2, ?_⟩
      · simp only [List.length_cons] at haCost
        simp only [List.length_append, List.length_singleton]
        nlinarith
      · simpa [multiplyFrom_append_bit, multiplyStep] using ht0
      · have heq := haFrame.2.2.2.2.2.1 3 (by omega)
        simpa [heq, ready, shiftedState] using ht3


/-- Original loop contract, with the retained input tape endpoint omitted. -/
theorem loop_simulation (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (hxs : 0 < xs.length) (remaining acc : List Bool) (B : ℕ)
    (s : BitRAMState) (ao xo zo yo : ℤ)
    (hxB : xs.length ≤ B) (haB : acc.length ≤ B)
    (hpc : s.pc = 2) (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : PrefixTape (s.tapes 3) remaining yo) :
    ∃ cost t resultOrigin scratchOrigin,
      cost ≤ 200 * (B + 2 * remaining.length + 4) * remaining.length + 4 ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 71 ∧
      t.tapes 0 = BitTape.shifted (multiplyFrom xs acc remaining) resultOrigin ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} := by
  obtain ⟨c, t, ro, so, hc, hs, hp, h0, h1, h2, _⟩ :=
    loop_simulation_full input tape xs hxs remaining acc B s ao xo zo yo hxB haB hpc h0 h1 h2 h3
  exact ⟨c, t, ro, so, hc, hs, hp, h0, h1, h2⟩

/-- Nonempty multiplicands leave the read-only multiplier one cell before
its word; this exact endpoint permits charged cleanup and reuse. -/
theorem simulation_nonempty_cleanup (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (ao xo zo yo : ℤ)
    (hxs : 0 < xs.length)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd ys yo) :
    ∃ cost t bits resultOrigin scratchOrigin,
      cost ≤ 400 * (xs.length + ys.length + 2) * (ys.length + 1) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 71 ∧
      t.tapes 0 = BitTape.shifted bits resultOrigin ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      addressValue bits = addressValue xs * addressValue ys ∧
      bits.length ≤ xs.length + 2 * ys.length ∧
      t.tapes 3 = {BitTape.shifted ys yo with head := yo - 1} := by
  have hi := initial_block input tape s hpc
  have hipc : (initialState s).pc = 2 := by
    cases xs with
    | nil => simp at hxs
    | cons x xs => simp [initialState, h1, BitTape.read, BitTape.shifted]
  obtain ⟨cost, t, ro, so, hc, hs, hp, ht0, ht1, ht2, ht3⟩ :=
    loop_simulation_full input tape xs hxs ys [] xs.length (initialState s) ao xo zo yo
      le_rfl (by simp) hipc (by simpa [initialState] using h0)
      (by simpa [initialState] using h1) (by simpa [initialState] using h2)
      (by simpa [initialState, h3] using PrefixTape.shiftedEnd ys yo)
  refine ⟨3 + cost, t, multiplyBits xs ys, ro, so, by nlinarith,
    hi.trans hs, hp, ?_, ht1, ht2, multiplyBits_value xs ys, multiplyBits_length_le xs ys, ?_⟩
  · simpa [multiplyFrom_empty] using ht0
  · simpa [initialState, h3, BitTape.shiftedEnd] using ht3

/-- The empty multiplicand takes the finite zero branch. Nonempty words use
exactly the same fixed program and the proved Horner loop above. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (ao xo zo yo : ℤ)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd ys yo) :
    ∃ cost t bits resultOrigin scratchOrigin,
      cost ≤ 400 * (xs.length + ys.length + 2) * (ys.length + 1) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 71 ∧
      t.tapes 0 = BitTape.shifted bits resultOrigin ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      addressValue bits = addressValue xs * addressValue ys ∧
      bits.length ≤ xs.length + 2 * ys.length := by
  have hi := initial_block input tape s hpc
  by_cases hx : xs = []
  · subst xs
    refine ⟨3, initialState s, [], ao, zo, by nlinarith, hi, ?_, ?_, ?_, ?_, by simp [addressValue], by simp⟩
    · simp [initialState, h1, BitTape.read, BitTape.blank]
    · simpa [initialState] using h0
    · simpa [initialState] using h1
    · simpa [initialState] using h2
  · have hlength : 0 < xs.length := by cases xs <;> simp_all
    have hipc : (initialState s).pc = 2 := by
      cases xs with
      | nil => contradiction
      | cons x xs => simp [initialState, h1, BitTape.read, BitTape.shifted]
    obtain ⟨cost, t, ro, so, hc, hs, hp, ht0, ht1, ht2⟩ :=
      loop_simulation input tape xs hlength ys [] xs.length (initialState s) ao xo zo yo
        le_rfl (by simp) hipc (by simpa [initialState] using h0)
        (by simpa [initialState] using h1) (by simpa [initialState] using h2)
        (by simpa [initialState, h3] using PrefixTape.shiftedEnd ys yo)
    refine ⟨3 + cost, t, multiplyBits xs ys, ro, so, by nlinarith,
      hi.trans hs, hp, ?_, ht1, ht2, multiplyBits_value xs ys, multiplyBits_length_le xs ys⟩
    simpa [multiplyFrom_empty] using ht0

/-- A single finite Boolean program computes products of arbitrary binary
words, with a proved quadratic cap in their bit lengths on every input and
random tape. There is no unit-cost multiplication instruction. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (ao xo zo yo : ℤ)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd ys yo) :
    ∃ t bits resultOrigin,
      (runPriced (program.next input tape)
        (400 * (xs.length + ys.length + 2) * (ys.length + 1) + 1) s).finished = some t ∧
      (runPriced (program.next input tape)
        (400 * (xs.length + ys.length + 2) * (ys.length + 1) + 1) s).instructions ≤
          400 * (xs.length + ys.length + 2) * (ys.length + 1) ∧
      t.tapes 0 = BitTape.shifted bits resultOrigin ∧
      addressValue bits = addressValue xs * addressValue ys ∧
      bits.length ≤ xs.length + 2 * ys.length := by
  obtain ⟨cost, t, bits, ro, so, hc, hs, hp, ht0, _, _, hv, hl⟩ :=
    simulation input tape s xs ys ao xo zo yo hpc h0 h1 h2 h3
  have halt : program.next input tape t = none := by
    simp [BitRAM.next, program, hp, RewindOvershoot.program, Rewind.program,
      RewindOvershoot.preamble, BitRAM.link, rippleAdder, TapeOps.clear,
      TapeOps.copyClear, BitRAMInstruction.relocate]
  have hr := hs.runPriced_ge halt
    (400 * (xs.length + ys.length + 2) * (ys.length + 1) + 1) (by omega)
  exact ⟨t, bits, ro, hr.1, by simpa [hr.2] using hc, ht0, hv, hl⟩

end Maxwell.Cost.HornerMultiply
