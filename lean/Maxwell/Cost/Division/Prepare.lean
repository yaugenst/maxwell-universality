import Maxwell.Cost.Division.Program

namespace Maxwell.Cost.Division

abbrev CycleFrame := HornerMultiply.addCycleFrame

theorem tapeOps_other_tape {source target : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame source target s t) (i : ℕ) (hs : i ≠ source) (ht : i ≠ target) :
    t.tapes i = s.tapes i := h.2.2.2.2.2.1 i hs ht

theorem tapeOps_borrow {source target : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame source target s t) : t.registers 2 = s.registers 2 :=
  h.2.2.2.2.2.2 2 (by decide) (by decide)

theorem CycleFrame.higher_tapes {s t : BitRAMState} (h : CycleFrame s t)
    (i : ℕ) (hi : 3 ≤ i) : t.tapes i = s.tapes i := h.2.2.2.2.2.1 i hi

/-- The actual subtraction and three scans leave all three words at their
starts, while retaining the subtractor's borrow in register 2. -/
theorem prepare (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (acc divisor : List Bool) (ao xo zo : ℤ)
    (hacc : 0 < acc.length) (hdivisor : 0 < divisor.length)
    (hpc : s.pc = 5)
    (h0 : s.tapes 0 = BitTape.shifted acc ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo}) :
    ∃ t, PricedSteps (program.next input tape)
        (32 * max acc.length divisor.length + 30) s t ∧ t.pc = 48 ∧
      t.registers 2 = (Subtraction.result false acc divisor).2 ∧
      t.tapes 0 = BitTape.shifted acc ao ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = BitTape.shifted (Subtraction.result false acc divisor).1 zo ∧
      CycleFrame s t := by
  let diff := (Subtraction.result false acc divisor).1
  let N := max acc.length divisor.length
  have hlen : diff.length = N := Subtraction.result_length false acc divisor
  obtain ⟨a, ha, hapc, hb, ha0, ha1, ha2, haf⟩ := Subtraction.words input tape
    {s with pc := 0} acc divisor ao xo zo rfl h0 h1 h2
  let sA : BitRAMState := {a with pc := 25}
  have hA : PricedSteps (program.next input tape) (20 * N + 9 + 1) s sA :=
    contains_subtract.call_at input tape s a hpc ha (by simp [Subtraction.program, hapc])
  have hAf : CycleFrame s sA := HornerMultiply.addCycleFrame_of_ripple haf

  let r0 := RewindOvershoot.finish 0 ao {sA with pc := 0}
  let sR0 : BitRAMState := {r0 with pc := 34}
  have hr0 := RewindOvershoot.shifted_steps 0 ao input tape acc N hacc
    (le_max_left _ _) {sA with pc := 0} rfl ha0
  have hR0 : PricedSteps (program.next input tape) (4 * N + 6 + 1) sA sR0 :=
    contains_rewind_remainder.call_at input tape sA r0 rfl hr0
      (by simp [r0, RewindOvershoot.finish, RewindOvershoot.program,
        BitRAM.link, RewindOvershoot.preamble, Rewind.program])
  have hR0f : CycleFrame sA sR0 :=
    HornerMultiply.finishAt_addCycleFrame 0 (by omega) ao {sA with pc := 0}
  have hr00 : sR0.tapes 0 = BitTape.shifted acc ao :=
    RewindOvershoot.finish_shifted 0 ao acc N {sA with pc := 0} ha0
  have hr01 : sR0.tapes 1 = {BitTape.shifted divisor xo with head := xo + N} := by
    simpa [sR0, r0, RewindOvershoot.finish, Rewind.finishAt, sA, N] using ha1
  have hr02 : sR0.tapes 2 = BitTape.shiftedEnd diff zo := by
    simpa [sR0, r0, RewindOvershoot.finish, Rewind.finishAt, sA] using ha2
  have hr0b : sR0.registers 2 = (Subtraction.result false acc divisor).2 := by
    simpa [sR0, r0, RewindOvershoot.finish, Rewind.finishAt, sA] using hb

  let r1 := RewindOvershoot.finish 1 xo {sR0 with pc := 0}
  let sR1 : BitRAMState := {r1 with pc := 43}
  have hr1 := RewindOvershoot.shifted_steps 1 xo input tape divisor N hdivisor
    (le_max_right _ _) {sR0 with pc := 0} rfl hr01
  have hR1 : PricedSteps (program.next input tape) (4 * N + 6 + 1) sR0 sR1 :=
    contains_rewind_divisor.call_at input tape sR0 r1 rfl hr1
      (by simp [r1, RewindOvershoot.finish, RewindOvershoot.program,
        BitRAM.link, RewindOvershoot.preamble, Rewind.program])
  have hR1f : CycleFrame sR0 sR1 :=
    HornerMultiply.finishAt_addCycleFrame 1 (by omega) xo {sR0 with pc := 0}
  have hr10 : sR1.tapes 0 = BitTape.shifted acc ao := by
    simpa [sR1, r1, RewindOvershoot.finish, Rewind.finishAt] using hr00
  have hr11 : sR1.tapes 1 = BitTape.shifted divisor xo :=
    RewindOvershoot.finish_shifted 1 xo divisor N {sR0 with pc := 0} hr01
  have hr12 : sR1.tapes 2 = BitTape.shiftedEnd diff zo := by
    simpa [sR1, r1, RewindOvershoot.finish, Rewind.finishAt] using hr02
  have hr1b : sR1.registers 2 = (Subtraction.result false acc divisor).2 := by
    simpa [sR1, r1, RewindOvershoot.finish, Rewind.finishAt] using hr0b

  let r2 := Rewind.finishAt 2 zo {sR1 with pc := 0}
  let sR2 : BitRAMState := {r2 with pc := 48}
  have hr2 := Rewind.shiftedEnd_steps 2 zo input tape diff {sR1 with pc := 0} rfl hr12
  have hR2 : PricedSteps (program.next input tape) (4 * diff.length + 5 + 1) sR1 sR2 :=
    contains_rewind_scratch.call_at input tape sR1 r2 rfl hr2
      (by simp [r2, Rewind.finishAt, Rewind.program])
  have hR2f : CycleFrame sR1 sR2 :=
    HornerMultiply.finishAt_addCycleFrame 2 (by omega) zo {sR1 with pc := 0}
  refine ⟨sR2, ?_, rfl, ?_, ?_, ?_, ?_, ((hAf.trans hR0f).trans hR1f).trans hR2f⟩
  · convert ((hA.trans hR0).trans hR1).trans hR2 using 1
    rw [hlen]
    dsimp [N]
    omega
  · simpa [sR2, r2, Rewind.finishAt] using hr1b
  · simpa [sR2, r2, Rewind.finishAt] using hr10
  · simpa [sR2, r2, Rewind.finishAt] using hr11
  · exact Rewind.finishAt_shiftedEnd 2 zo diff {sR1 with pc := 0} hr12

end Maxwell.Cost.Division
