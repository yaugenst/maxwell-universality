import Maxwell.Cost.Division.Prepare

namespace Maxwell.Cost.Division

/-- The borrow path preserves the unreduced remainder and clears the scratch word. -/
theorem underflow_cleanup (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (acc divisor diff : List Bool) (ao xo zo : ℤ)
    (hpc : s.pc = 49) (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = BitTape.shifted diff zo) :
    ∃ t, PricedSteps (program.next input tape) (6 * diff.length + 5) s t ∧
      t.pc = 76 ∧ t.registers 2 = s.registers 2 ∧
      t.tapes 0 = BitTape.shifted acc ao ∧ t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + diff.length} ∧ CycleFrame s t := by
  obtain ⟨c, hc, hcpc, hc2, hcf⟩ := TapeOps.clear_steps 2 input tape diff zo
    {s with pc := 0} rfl h2
  let sC : BitRAMState := {c with pc := 55}
  have hC : PricedSteps (program.next input tape) (6 * diff.length + 3 + 1) s sC :=
    contains_clear_scratch.call_at input tape s c hpc hc (by simp [TapeOps.clear, hcpc])
  have hfooter : PricedSteps (program.next input tape) 1 sC {sC with pc := 76} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, sC, Subtraction.program,
      RewindOvershoot.program, RewindOvershoot.preamble, BitRAM.link, Rewind.program,
      TapeOps.clear, TapeOps.copyClear, BitRAMInstruction.relocate]
  refine ⟨{sC with pc := 76}, ?_, rfl, tapeOps_borrow hcf,
    (tapeOps_other_tape hcf 0 (by omega) (by omega)).trans h0,
    (tapeOps_other_tape hcf 1 (by omega) (by omega)).trans h1, hc2,
    HornerMultiply.addCycleFrame_of_tapeOps (by omega) (by omega) hcf⟩
  convert hC.trans hfooter using 1

/-- The nonborrow path replaces the old remainder by the actual subtraction
word, and clears both old storage regions by charged tape instructions. -/
theorem success_cleanup (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (acc divisor diff : List Bool) (ao xo zo : ℤ)
    (hpc : s.pc = 56) (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = BitTape.shifted diff zo) :
    ∃ t, PricedSteps (program.next input tape) (6 * acc.length + 12 * diff.length + 15) s t ∧
      t.pc = 76 ∧ t.registers 2 = s.registers 2 ∧
      t.tapes 0 = BitTape.shifted diff (ao + acc.length) ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + diff.length} ∧ CycleFrame s t := by
  obtain ⟨c, hc, hcpc, hc0, hcf⟩ := TapeOps.clear_steps 0 input tape acc ao
    {s with pc := 0} rfl h0
  let sC : BitRAMState := {c with pc := 62}
  have hC : PricedSteps (program.next input tape) (6 * acc.length + 3 + 1) s sC :=
    contains_clear_remainder.call_at input tape s c hpc hc (by simp [TapeOps.clear, hcpc])
  have hCf : CycleFrame s sC :=
    HornerMultiply.addCycleFrame_of_tapeOps (by omega) (by omega) hcf
  have hc1 : sC.tapes 1 = BitTape.shifted divisor xo :=
    (tapeOps_other_tape hcf 1 (by omega) (by omega)).trans h1
  have hc2 : sC.tapes 2 = BitTape.shifted diff zo :=
    (tapeOps_other_tape hcf 2 (by omega) (by omega)).trans h2
  have hcb : sC.registers 2 = s.registers 2 := tapeOps_borrow hcf
  obtain ⟨cp, hcp, hcppc, hcp2, hcp0, hcpf⟩ := TapeOps.copyClear_to_blank_steps 2 0 (by omega)
    input tape diff zo (ao + acc.length) {sC with pc := 0} rfl hc2 hc0
  let sCP : BitRAMState := {cp with pc := 70}
  have hCP : PricedSteps (program.next input tape) (8 * diff.length + 3 + 1) sC sCP :=
    contains_copy.call_at input tape sC cp rfl hcp (by simp [TapeOps.copyClear, hcppc])
  have hCPf : CycleFrame sC sCP :=
    HornerMultiply.addCycleFrame_of_tapeOps (by omega) (by omega) hcpf
  have hcp1 : sCP.tapes 1 = BitTape.shifted divisor xo :=
    (tapeOps_other_tape hcpf 1 (by omega) (by omega)).trans hc1
  have hcpb : sCP.registers 2 = s.registers 2 := (tapeOps_borrow hcpf).trans hcb
  let ra := Rewind.finishAt 0 (ao + acc.length) {sCP with pc := 0}
  let sRA : BitRAMState := {ra with pc := 75}
  have hra := Rewind.shiftedEnd_steps 0 (ao + acc.length) input tape diff
    {sCP with pc := 0} rfl hcp0
  have hRA : PricedSteps (program.next input tape) (4 * diff.length + 5 + 1) sCP sRA :=
    contains_rewind_result.call_at input tape sCP ra rfl hra
      (by simp [ra, Rewind.finishAt, Rewind.program])
  have hRAf : CycleFrame sCP sRA :=
    HornerMultiply.finishAt_addCycleFrame 0 (by omega) (ao + acc.length) {sCP with pc := 0}
  have hra0 : sRA.tapes 0 = BitTape.shifted diff (ao + acc.length) :=
    Rewind.finishAt_shiftedEnd 0 (ao + acc.length) diff {sCP with pc := 0} hcp0
  have hra1 : sRA.tapes 1 = BitTape.shifted divisor xo := by
    simpa [sRA, ra, Rewind.finishAt] using hcp1
  have hra2 : sRA.tapes 2 = {BitTape.blank with head := zo + diff.length} := by
    simpa [sRA, ra, Rewind.finishAt, sCP] using hcp2
  have hrab : sRA.registers 2 = s.registers 2 := by
    simpa [sRA, ra, Rewind.finishAt] using hcpb
  have hfooter : PricedSteps (program.next input tape) 1 sRA {sRA with pc := 76} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, sRA, Subtraction.program,
      RewindOvershoot.program, RewindOvershoot.preamble, BitRAM.link, Rewind.program,
      TapeOps.clear, TapeOps.copyClear, BitRAMInstruction.relocate]
  refine ⟨{sRA with pc := 76}, ?_, rfl, hrab, hra0, hra1, hra2,
    (hCf.trans hCPf).trans hRAf⟩
  convert ((hC.trans hCP).trans hRA).trans hfooter using 1
  omega

/-- One complete remainder reduction in the fixed program, including the
borrow branch and both charged transfer paths. -/
theorem reduceCycle (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (acc divisor : List Bool) (ao xo zo : ℤ)
    (hacc : 0 < acc.length) (hdivisor : 0 < divisor.length)
    (hpc : s.pc = 5) (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ cost t origin, cost ≤ 100 * (max acc.length divisor.length + 2) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 76 ∧
      t.registers 2 = (Subtraction.result false acc divisor).2 ∧
      t.tapes 0 = BitTape.shifted
        (if (Subtraction.result false acc divisor).2 then acc
          else (Subtraction.result false acc divisor).1) origin ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + max acc.length divisor.length} ∧
      CycleFrame s t := by
  obtain ⟨p, hp, hppc, hpb, hp0, hp1, hp2, hpf⟩ :=
    prepare input tape s acc divisor ao xo zo hacc hdivisor hpc h0 h1 h2
  let diff := (Subtraction.result false acc divisor).1
  have hlen : diff.length = max acc.length divisor.length :=
    Subtraction.result_length false acc divisor
  cases hb : (Subtraction.result false acc divisor).2
  · have hbranch : PricedSteps (program.next input tape) 1 p {p with pc := 56} := by
      apply executeInstructions_sound (instructions := 1)
      simp [executeInstructions, BitRAM.next, program, hppc, hpb, hb, Subtraction.program,
        RewindOvershoot.program, RewindOvershoot.preamble, BitRAM.link, Rewind.program,
        TapeOps.clear, TapeOps.copyClear, BitRAMInstruction.relocate]
    obtain ⟨t, ht, htpc, htb, ht0, ht1, ht2, htf⟩ :=
      success_cleanup input tape {p with pc := 56} acc divisor diff ao xo zo rfl hp0 hp1 hp2
    refine ⟨_, t, ao + acc.length, ?_, (hp.trans hbranch).trans ht, htpc,
      (by simpa [hb] using htb.trans hpb), ?_, ht1, ?_, hpf.trans htf⟩
    · have := le_max_left acc.length divisor.length
      omega
    · simpa [hb] using ht0
    · simpa [hlen] using ht2
  · have hbranch : PricedSteps (program.next input tape) 1 p {p with pc := 49} := by
      apply executeInstructions_sound (instructions := 1)
      simp [executeInstructions, BitRAM.next, program, hppc, hpb, hb, Subtraction.program,
        RewindOvershoot.program, RewindOvershoot.preamble, BitRAM.link, Rewind.program,
        TapeOps.clear, TapeOps.copyClear, BitRAMInstruction.relocate]
    obtain ⟨t, ht, htpc, htb, ht0, ht1, ht2, htf⟩ :=
      underflow_cleanup input tape {p with pc := 49} acc divisor diff ao xo zo rfl hp0 hp1 hp2
    refine ⟨_, t, ao, ?_, (hp.trans hbranch).trans ht, htpc, (by simpa [hb] using htb.trans hpb),
      ?_, ht1, ?_, hpf.trans htf⟩
    · omega
    · simpa [hb] using ht0
    · simpa [hlen] using ht2

end Maxwell.Cost.Division
