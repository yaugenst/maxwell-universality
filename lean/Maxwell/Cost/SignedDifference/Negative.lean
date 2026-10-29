import Maxwell.Cost.SignedDifference.Program
import Maxwell.Cost.Multiplication.AddCycle

namespace Maxwell.Cost.SignedDifference

open HornerMultiply (addCycleFrame addCycleFrame_of_ripple addCycleFrame_of_tapeOps finishAt_addCycleFrame)

/-- The negative branch clears the wrapped output and computes the reverse
unsigned difference. It preserves the sign captured before this branch. -/
theorem negativeCycle_full (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys output : List Bool) (xo yo zo : ℤ)
    (hxpos : 0 < xs.length) (hypos : 0 < ys.length)
    (hlen : output.length = max xs.length ys.length) (hpc : s.pc = 33)
    (h0 : s.tapes 0 = {BitTape.shifted xs xo with head := xo + max xs.length ys.length})
    (h1 : s.tapes 1 = {BitTape.shifted ys yo with head := yo + max xs.length ys.length})
    (h2 : s.tapes 2 = BitTape.shiftedEnd output zo) :
    ∃ t, PricedSteps (program.next input tape) (38 * max xs.length ys.length + 34) s t ∧
      t.pc = 82 ∧
      t.tapes 2 = BitTape.shiftedEnd (Subtraction.result false ys xs).1 (zo + output.length) ∧
      addCycleFrame s t ∧
      t.tapes 0 = {BitTape.shifted xs xo with head := xo + max xs.length ys.length} ∧
      t.tapes 1 = {BitTape.shifted ys yo with head := yo + max xs.length ys.length} := by
  let N := max xs.length ys.length
  let r0 := RewindOvershoot.finish 0 xo {s with pc := 0}
  let s0 : BitRAMState := {r0 with pc := 42}
  have hr0 := RewindOvershoot.shifted_steps 0 xo input tape xs N hxpos (le_max_left _ _)
    {s with pc := 0} rfl h0
  have hs0 : PricedSteps (program.next input tape) (4 * N + 7) s s0 := by
    simpa [Nat.add_assoc] using contains_rewind_left.call_at input tape s r0 hpc hr0
      (by simp [r0, RewindOvershoot.finish, RewindOvershoot.program, BitRAM.link,
        RewindOvershoot.preamble, Rewind.program])
  have hf0 : addCycleFrame s s0 := finishAt_addCycleFrame 0 (by omega) xo {s with pc := 0}
  have h00 : s0.tapes 0 = BitTape.shifted xs xo :=
    RewindOvershoot.finish_shifted 0 xo xs N {s with pc := 0} h0
  have h01 : s0.tapes 1 = {BitTape.shifted ys yo with head := yo + N} := by
    simpa [s0, r0, RewindOvershoot.finish, Rewind.finishAt, N] using h1
  have h02 : s0.tapes 2 = BitTape.shiftedEnd output zo := by
    simpa [s0, r0, RewindOvershoot.finish, Rewind.finishAt] using h2
  let r1 := RewindOvershoot.finish 1 yo {s0 with pc := 0}
  let s1 : BitRAMState := {r1 with pc := 51}
  have hr1 := RewindOvershoot.shifted_steps 1 yo input tape ys N hypos (le_max_right _ _)
    {s0 with pc := 0} rfl h01
  have hs1 : PricedSteps (program.next input tape) (4 * N + 7) s0 s1 := by
    simpa [Nat.add_assoc] using contains_rewind_right.call_at input tape s0 r1 rfl hr1
      (by simp [r1, RewindOvershoot.finish, RewindOvershoot.program, BitRAM.link,
        RewindOvershoot.preamble, Rewind.program])
  have hf1 : addCycleFrame s0 s1 := finishAt_addCycleFrame 1 (by omega) yo {s0 with pc := 0}
  have h10 : s1.tapes 0 = BitTape.shifted xs xo := by
    simpa [s1, r1, RewindOvershoot.finish, Rewind.finishAt] using h00
  have h11 : s1.tapes 1 = BitTape.shifted ys yo :=
    RewindOvershoot.finish_shifted 1 yo ys N {s0 with pc := 0} h01
  have h12 : s1.tapes 2 = BitTape.shiftedEnd output zo := by
    simpa [s1, r1, RewindOvershoot.finish, Rewind.finishAt] using h02
  let r2 := Rewind.finishAt 2 zo {s1 with pc := 0}
  let s2 : BitRAMState := {r2 with pc := 56}
  have hr2 := Rewind.shiftedEnd_steps 2 zo input tape output {s1 with pc := 0} rfl h12
  have hs2 : PricedSteps (program.next input tape) (4 * N + 6) s1 s2 := by
    simpa [N, hlen, Nat.add_assoc] using contains_rewind_output.call_at input tape s1 r2 rfl hr2
      (by simp [r2, Rewind.finishAt, Rewind.program])
  have hf2 : addCycleFrame s1 s2 := finishAt_addCycleFrame 2 (by omega) zo {s1 with pc := 0}
  have h20 : s2.tapes 0 = BitTape.shifted xs xo := by
    simpa [s2, r2, Rewind.finishAt] using h10
  have h21 : s2.tapes 1 = BitTape.shifted ys yo := by
    simpa [s2, r2, Rewind.finishAt] using h11
  have h22 : s2.tapes 2 = BitTape.shifted output zo :=
    Rewind.finishAt_shiftedEnd 2 zo output {s1 with pc := 0} h12
  obtain ⟨cleared, hclear, hcpc, hctape, hcframe⟩ :=
    TapeOps.clear_steps 2 input tape output zo {s2 with pc := 0} rfl h22
  let s3 : BitRAMState := {cleared with pc := 62}
  have hs3 : PricedSteps (program.next input tape) (6 * N + 4) s2 s3 := by
    simpa [N, hlen, Nat.add_assoc] using contains_clear.call_at input tape s2 cleared rfl hclear
      (by simp [TapeOps.clear, hcpc])
  have hf3 : addCycleFrame s2 s3 := addCycleFrame_of_tapeOps (by omega) (by omega) hcframe
  have h30 : s3.tapes 0 = BitTape.shifted xs xo := by
    exact (hcframe.2.2.2.2.2.1 0 (by omega) (by omega)).trans h20
  have h31 : s3.tapes 1 = BitTape.shifted ys yo := by
    exact (hcframe.2.2.2.2.2.1 1 (by omega) (by omega)).trans h21
  obtain ⟨subtracted, hsub, hspc, _, hs0word, hs1word, hstape, hsframe⟩ :=
    Subtraction.swapped_words input tape {s3 with pc := 0} xs ys xo yo (zo + output.length)
      rfl h30 h31 hctape
  let final : BitRAMState := {subtracted with pc := 82}
  have hs4 : PricedSteps (program.next input tape) (20 * N + 10) s3 final := by
    simpa [N, max_comm, Nat.add_assoc] using contains_reverse_subtract.call_at input tape
      s3 subtracted rfl hsub
      (by simp [Subtraction.swappedProgram, BitRAM.renameTapes, Subtraction.program, hspc,
        BitRAMInstruction.renameTapes])
  have hf4 : addCycleFrame s3 final := addCycleFrame_of_ripple hsframe
  refine ⟨final, ?_, rfl, hstape, (((hf0.trans hf1).trans hf2).trans hf3).trans hf4,
    by simpa [final, max_comm] using hs0word,
    by simpa [final, max_comm] using hs1word⟩
  convert (((hs0.trans hs1).trans hs2).trans hs3).trans hs4 using 1
  simp [N]
  omega

/-- Compatibility projection retaining the original negative-branch API. -/
theorem negativeCycle (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys output : List Bool) (xo yo zo : ℤ)
    (hxpos : 0 < xs.length) (hypos : 0 < ys.length)
    (hlen : output.length = max xs.length ys.length) (hpc : s.pc = 33)
    (h0 : s.tapes 0 = {BitTape.shifted xs xo with head := xo + max xs.length ys.length})
    (h1 : s.tapes 1 = {BitTape.shifted ys yo with head := yo + max xs.length ys.length})
    (h2 : s.tapes 2 = BitTape.shiftedEnd output zo) :
    ∃ t, PricedSteps (program.next input tape) (38 * max xs.length ys.length + 34) s t ∧
      t.pc = 82 ∧
      t.tapes 2 = BitTape.shiftedEnd (Subtraction.result false ys xs).1 (zo + output.length) ∧
      addCycleFrame s t := by
  obtain ⟨t, hs, hp, ht, hf, _, _⟩ := negativeCycle_full input tape s xs ys output xo yo zo
    hxpos hypos hlen hpc h0 h1 h2
  exact ⟨t, hs, hp, ht, hf⟩

end Maxwell.Cost.SignedDifference
