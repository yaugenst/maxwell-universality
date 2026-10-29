import Maxwell.Cost.SignedDifference.Negative
import Maxwell.Cost.Counter

namespace Maxwell.Cost.SignedDifference

def branchState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := if s.registers 2 then 33 else 82
    registers := Function.update s.registers 23 (s.registers 2)}

set_option maxRecDepth 4096 in
theorem branch_steps (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 30) :
    PricedSteps (program.next input tape) 3 s (branchState s) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, program, BitRAM.next, hpc, branchState,
    BitRAMState.setRegister, padProgram, Subtraction.program, BitRAMInstruction.relocate]

/-- Both signs are implemented by the same finite code. The zero case has
sign false, and the returned magnitude is the canonical codec word. -/
theorem simulation_cleanup (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xo yo zo : ℤ)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = BitTape.shifted xs xo)
    (h1 : s.tapes 1 = BitTape.shifted ys yo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ cost t origin,
      cost ≤ 100 * (max xs.length ys.length + 2) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 91 ∧
      t.registers 23 = sign xs ys ∧
      t.tapes 2 = BitTape.shiftedEnd (addressValue (magnitude xs ys)).bits origin ∧
      t.tapes 0 = {BitTape.shifted (padded xs) xo with
        head := xo + max (padded xs).length (padded ys).length} ∧
      t.tapes 1 = {BitTape.shifted (padded ys) yo with
        head := yo + max (padded xs).length (padded ys).length} := by
  let left := padFinal 0 {s with pc := 0}
  let s0 : BitRAMState := {left with pc := 5}
  have hl := pad_steps 0 input tape {s with pc := 0} xs xo rfl h0
  have hs0 := contains_pad_left.call_at input tape s left hpc hl
    (by simp [left, padProgram])
  have h00 : s0.tapes 0 = BitTape.shifted (padded xs) xo :=
    padFinal_tape 0 {s with pc := 0} xs xo h0
  have h01 : s0.tapes 1 = BitTape.shifted ys yo := by
    exact (padFinal_other_tape 0 1 {s with pc := 0} (by omega)).trans h1
  have h02 : s0.tapes 2 = {BitTape.blank with head := zo} := by
    exact (padFinal_other_tape 0 2 {s with pc := 0} (by omega)).trans h2
  let right := padFinal 1 {s0 with pc := 0}
  let s1 : BitRAMState := {right with pc := 10}
  have hr := pad_steps 1 input tape {s0 with pc := 0} ys yo rfl h01
  have hs1 := contains_pad_right.call_at input tape s0 right rfl hr
    (by simp [right, padProgram])
  have h10 : s1.tapes 0 = BitTape.shifted (padded xs) xo := by
    exact (padFinal_other_tape 1 0 {s0 with pc := 0} (by omega)).trans h00
  have h11 : s1.tapes 1 = BitTape.shifted (padded ys) yo :=
    padFinal_tape 1 {s0 with pc := 0} ys yo h01
  have h12 : s1.tapes 2 = {BitTape.blank with head := zo} := by
    exact (padFinal_other_tape 1 2 {s0 with pc := 0} (by omega)).trans h02
  let N := max (padded xs).length (padded ys).length
  obtain ⟨a, hasub, hapc, haborrow, ha0, ha1, ha2, _⟩ :=
    Subtraction.words input tape {s1 with pc := 0} (padded xs) (padded ys) xo yo zo rfl h10 h11 h12
  let s2 : BitRAMState := {a with pc := 30}
  have hs2 := contains_subtract.call_at input tape s1 a rfl hasub
    (by simp [Subtraction.program, hapc])
  have hborrow : s2.registers 2 = sign xs ys := haborrow
  have hb := branch_steps input tape s2 rfl
  have hmiddle : ∃ middleCost middle origin,
      middleCost ≤ 38 * N + 37 ∧
      PricedSteps (program.next input tape) middleCost s2 middle ∧ middle.pc = 82 ∧
      middle.registers 23 = sign xs ys ∧
      middle.tapes 2 = BitTape.shiftedEnd (magnitude xs ys) origin ∧
      middle.tapes 0 = {BitTape.shifted (padded xs) xo with head := xo + N} ∧
      middle.tapes 1 = {BitTape.shifted (padded ys) yo with head := yo + N} := by
    cases hsign : sign xs ys with
    | false =>
      refine ⟨3, branchState s2, zo, by omega, hb, ?_, ?_, ?_, ha0, ha1⟩
      · simp [branchState, hborrow, hsign]
      · simp [branchState, hborrow, hsign]
      · simpa [branchState, magnitude, hsign, s2] using ha2
    | true =>
      obtain ⟨middle, hm, hmpc, hm2, hmframe, hm0, hm1⟩ :=
        negativeCycle_full input tape (branchState s2) (padded xs) (padded ys)
          (Subtraction.result false (padded xs) (padded ys)).1 xo yo zo
          (padded_pos xs) (padded_pos ys) (Subtraction.result_length _ _ _)
          (by simp [branchState, hborrow, hsign]) ha0 ha1 ha2
      refine ⟨3 + (38 * N + 34), middle, zo + N, by omega, hb.trans hm, hmpc, ?_, ?_, hm0, hm1⟩
      · have hg := hmframe.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega)
        simpa [branchState, hborrow, hsign] using hg
      · simpa [magnitude, hsign, Subtraction.result_length, N] using hm2
  obtain ⟨middleCost, middle, origin, hmc, hms, hmpc, hmsg, hmt, hm0, hm1⟩ := hmiddle
  obtain ⟨trimCost, trimmed, htc, hts, htpc, htt, _, htf⟩ :=
    TapeOps.trim_shifted_canonical_steps 2 origin input tape (magnitude xs ys)
      {middle with pc := 0} rfl hmt
  let final : BitRAMState := {trimmed with pc := 91}
  have hsf := contains_trim.call_at input tape middle trimmed hmpc hts
    (by simp [TapeOps.trim, htpc])
  refine ⟨padCost xs + 1 + (padCost ys + 1) + (20 * N + 9 + 1) + middleCost +
      (trimCost + 1), final, origin, ?_, (((hs0.trans hs1).trans hs2).trans hms).trans hsf,
      rfl, ?_, htt, ?_, ?_⟩
  · have hpx := pad_cost_le xs
    have hpy := pad_cost_le ys
    have hn : N ≤ max xs.length ys.length + 1 := by
      have hnx := padded_length xs
      have hny := padded_length ys
      dsimp [N]
      omega
    rw [magnitude_length] at htc
    dsimp [N] at hmc ⊢
    omega
  · exact (htf.2.2.2.2.2.2 23 (by omega) (by omega)).trans hmsg
  · exact (htf.2.2.2.2.2.1 0 (by omega) (by omega)).trans hm0
  · exact (htf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hm1

/-- Original output-only interface, projected from the complete tape-state proof. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xo yo zo : ℤ)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = BitTape.shifted xs xo)
    (h1 : s.tapes 1 = BitTape.shifted ys yo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ cost t origin,
      cost ≤ 100 * (max xs.length ys.length + 2) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 91 ∧
      t.registers 23 = sign xs ys ∧
      t.tapes 2 = BitTape.shiftedEnd (addressValue (magnitude xs ys)).bits origin := by
  obtain ⟨cost, t, origin, hc, hs, hp, hg, ht, _, _⟩ :=
    simulation_cleanup input tape s xs ys xo yo zo hpc h0 h1 h2
  exact ⟨cost, t, origin, hc, hs, hp, hg, ht⟩

/-- The actual capped execution returns a canonical magnitude and a sign
whose signed value is exactly the integer difference. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (xo yo zo : ℤ)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = BitTape.shifted xs xo)
    (h1 : s.tapes 1 = BitTape.shifted ys yo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ t origin, (runPriced (program.next input tape) (100 * (max xs.length ys.length + 2) + 1) s).finished = some t ∧
      (runPriced (program.next input tape) (100 * (max xs.length ys.length + 2) + 1) s).instructions ≤
        100 * (max xs.length ys.length + 2) ∧
      t.tapes 2 = BitTape.shiftedEnd (addressValue (magnitude xs ys)).bits origin ∧
      (if t.registers 23 then -(addressValue (magnitude xs ys) : ℤ)
        else (addressValue (magnitude xs ys) : ℤ)) =
        (addressValue xs : ℤ) - (addressValue ys : ℤ) ∧
      (addressValue (magnitude xs ys) = 0 → t.registers 23 = false) := by
  obtain ⟨cost, t, origin, hc, hs, hp, hg, ht⟩ := simulation input tape s xs ys xo yo zo hpc h0 h1 h2
  have halt : program.next input tape t = none := by
    simp [program, BitRAM.next, hp, padProgram, Subtraction.program, Subtraction.swappedProgram,
      BitRAM.renameTapes, RewindOvershoot.program, RewindOvershoot.preamble,
      Rewind.program, BitRAM.link, TapeOps.clear, TapeOps.trim, BitRAMInstruction.relocate]
  have hr := hs.runPriced_ge halt (100 * (max xs.length ys.length + 2) + 1) (by omega)
  exact ⟨t, origin, hr.1, by simpa [hr.2] using hc, ht,
    by rw [hg]; exact signed_value xs ys, fun hz => hg.trans (zero_sign xs ys hz)⟩

end Maxwell.Cost.SignedDifference
