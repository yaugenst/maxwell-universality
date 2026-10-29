import Maxwell.Cost.Counter

/-! An actual finite counter loop around an actual finite body program.
The body contract describes proved executions; it adds no interpreter
instruction or host-language continuation. -/

namespace Maxwell.Cost.CountedLoop

def counter : BitRAM := Counter.programOn 14

def exitPC (body : BitRAM) : ℕ := 17 + body.code.length

def bodyPreamble (body : BitRAM) : List BitRAMInstruction :=
  counter.code.map (BitRAMInstruction.relocate 0 16) ++ [.branch 2 (exitPC body) 17]

def counterSuffix (body : BitRAM) : List BitRAMInstruction :=
  [.branch 2 (exitPC body) 17] ++ body.code.map (BitRAMInstruction.relocate 17 0) ++ [.halt]

def program (body : BitRAM) : BitRAM := BitRAM.link [] counter 16 (counterSuffix body)

theorem counter_length : counter.code.length = 16 := by
  simp [counter, Counter.programOn, BitRAM.renameTapes, Counter.program, BitRAM.link,
    Counter.counterSuffix, binaryCounter, Rewind.program]

theorem bodyPreamble_length (body : BitRAM) : (bodyPreamble body).length = 17 := by
  simp [bodyPreamble, counter_length]

theorem program_as_body (body : BitRAM) :
    program body = BitRAM.link (bodyPreamble body) body 0 [.halt] := by
  simp only [program, BitRAM.link, bodyPreamble_length]
  simp [bodyPreamble, counterSuffix, List.append_assoc]

theorem exit_instruction (body : BitRAM) : (program body).code[exitPC body]? = some .halt := by
  rw [program_as_body]
  simp [BitRAM.link, exitPC, bodyPreamble_length]

theorem branch_instruction (body : BitRAM) :
    (program body).code[16]? = some (.branch 2 (exitPC body) 17) := by
  simp [program, BitRAM.link, counterSuffix, counter_length]

theorem counter_halt : counter.code[15]? = some .halt := by decide

def decisionState (body : BitRAM) (s : BitRAMState) : BitRAMState :=
  {s with pc := if s.registers 2 then exitPC body else 17}

theorem counter_phase (body : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    (xs : List Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes 14 = BitTape.ofList xs) :
    ∃ final : BitRAMState,
      PricedSteps ((program body).next input tape) (13 * xs.length + 13) initial final ∧
      final.pc = (if final.registers 2 then exitPC body else 17) ∧
      final.tapes 14 = BitTape.ofList (subtractBit true xs) ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧
      Counter.FrameAt 14 initial final := by
  obtain ⟨s, hs, hspc, _, hstape, hzero, _, hframe⟩ :=
    Counter.steps_on 14 input tape xs initial hpc hword
  have hlinked := hs.link [] 16 (counterSuffix body)
  simp only [List.length_nil, BitRAMState.relocate, Nat.zero_add] at hlinked
  change PricedSteps ((program body).next input tape) _ initial s at hlinked
  have hreturn : PricedSteps ((program body).next input tape) 1 s {s with pc := 16} := by
    simpa only [List.length_nil, BitRAMState.relocate, Nat.zero_add, program] using
      (PricedSteps.step (BitRAM.link_return [] counter 16 (counterSuffix body) input tape s
        (by simpa [hspc] using counter_halt)) (PricedSteps.refl _))
  have hbranch : PricedSteps ((program body).next input tape) 1
      {s with pc := 16} (decisionState body s) := by
    exact PricedSteps.step (by simp [BitRAM.next, branch_instruction, decisionState])
      (PricedSteps.refl _)
  refine ⟨decisionState body s, ?_, rfl, hstape, hzero, hframe⟩
  convert (hlinked.trans hreturn).trans hbranch using 1

theorem body_phase (body : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState} (hpc : s.pc = 17)
    (hbody : PricedSteps (body.next input tape) cost {s with pc := 0} t)
    (hhalt : body.code[t.pc]? = some .halt) :
    PricedSteps ((program body).next input tape) (cost + 1) s {t with pc := 0} := by
  have hlinked := hbody.link (bodyPreamble body) 0 [.halt]
  rw [← program_as_body, bodyPreamble_length] at hlinked
  have hstart : ({s with pc := 0} : BitRAMState).relocate 17 = s := by
    cases s
    simp_all [BitRAMState.relocate]
  rw [hstart] at hlinked
  have hreturn : PricedSteps ((program body).next input tape) 1
      (t.relocate 17) {t with pc := 0} := by
    rw [program_as_body]
    simpa only [bodyPreamble_length] using
      (PricedSteps.step (BitRAM.link_return (bodyPreamble body) body 0 [.halt] input tape t hhalt)
        (PricedSteps.refl _))
  exact hlinked.trans hreturn

theorem frame_pc (s : BitRAMState) (pc : ℕ) : Counter.FrameAt 14 s {s with pc := pc} := by
  simp [Counter.FrameAt]

/-- A concrete body's execution contract is composed with the concrete
countdown loop. The invariant may describe a stored record log or another
proved construction state, provided counter scratch operations preserve it.
Every body invocation, counter pass, branch, and return is charged. -/
theorem simulation (body : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    (Invariant : ℕ → BitRAMState → Prop) (bodyBound : ℕ)
    (stable : ∀ n s t, Counter.FrameAt 14 s t → Invariant n s → Invariant n t)
    (bodyCorrect : ∀ n xs s, s.pc = 0 → addressValue xs = n →
      s.tapes 14 = BitTape.ofList xs → Invariant (n + 1) s →
      ∃ cost t, cost ≤ bodyBound ∧ PricedSteps (body.next input tape) cost s t ∧
        body.code[t.pc]? = some .halt ∧ t.tapes 14 = s.tapes 14 ∧ Invariant n t)
    (n : ℕ) (xs : List Bool) (initial : BitRAMState)
    (hpc : initial.pc = 0) (hvalue : addressValue xs = n)
    (hword : initial.tapes 14 = BitTape.ofList xs) (hinvariant : Invariant n initial) :
    ∃ cost final,
      PricedSteps ((program body).next input tape) cost initial final ∧
      cost ≤ (n + 1) * (13 * xs.length + 13) + n * (bodyBound + 1) ∧
      final.pc = exitPC body ∧ Invariant 0 final := by
  induction n generalizing xs initial with
  | zero =>
    obtain ⟨s, hs, hspc, _, hzero, hframe⟩ := counter_phase body input tape xs initial hpc hword
    have hflag := hzero.mpr hvalue
    refine ⟨13 * xs.length + 13, s, hs, ?_, ?_, stable 0 initial s hframe hinvariant⟩
    · simp
    · simpa [hflag] using hspc
  | succ n ih =>
    obtain ⟨s, hs, hspc, hsword, hzero, hframe⟩ := counter_phase body input tape xs initial hpc hword
    have hflag : s.registers 2 = false := by
      apply Bool.eq_false_iff.mpr
      intro hf
      have hv := hzero.mp hf
      omega
    have hbodyPC : s.pc = 17 := by simpa [hflag] using hspc
    have hpred : addressValue (subtractBit true xs) = n := by
      rw [subtractBit_pred xs (by omega), hvalue]
      omega
    have hinv := stable (n + 1) initial s hframe hinvariant
    have hinvLocal := stable (n + 1) s {s with pc := 0} (frame_pc s 0) hinv
    obtain ⟨bodyCost, t, hbound, hbody, hhalt, htword, htinv⟩ :=
      bodyCorrect n (subtractBit true xs) {s with pc := 0} rfl hpred hsword hinvLocal
    have hbodySteps := body_phase body input tape hbodyPC hbody hhalt
    have htinvLocal := stable n t {t with pc := 0} (frame_pc t 0) htinv
    obtain ⟨restCost, final, hrest, hrestBound, hfinal, hinvFinal⟩ :=
      ih (subtractBit true xs) {t with pc := 0} rfl hpred (htword.trans hsword) htinvLocal
    refine ⟨(13 * xs.length + 13) + (bodyCost + 1) + restCost, final,
      (hs.trans hbodySteps).trans hrest, ?_, hfinal, hinvFinal⟩
    simp only [subtractBit_length] at hrestBound
    nlinarith

theorem run (body : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    (Invariant : ℕ → BitRAMState → Prop) (bodyBound : ℕ)
    (stable : ∀ n s t, Counter.FrameAt 14 s t → Invariant n s → Invariant n t)
    (bodyCorrect : ∀ n xs s, s.pc = 0 → addressValue xs = n →
      s.tapes 14 = BitTape.ofList xs → Invariant (n + 1) s →
      ∃ cost t, cost ≤ bodyBound ∧ PricedSteps (body.next input tape) cost s t ∧
        body.code[t.pc]? = some .halt ∧ t.tapes 14 = s.tapes 14 ∧ Invariant n t)
    (n : ℕ) (xs : List Bool) (initial : BitRAMState)
    (hpc : initial.pc = 0) (hvalue : addressValue xs = n)
    (hword : initial.tapes 14 = BitTape.ofList xs) (hinvariant : Invariant n initial) :
    ∃ final,
      (runPriced ((program body).next input tape)
        ((n + 1) * (13 * xs.length + 13) + n * (bodyBound + 1) + 1) initial).finished =
          some final ∧
      (runPriced ((program body).next input tape)
        ((n + 1) * (13 * xs.length + 13) + n * (bodyBound + 1) + 1) initial).instructions ≤
          (n + 1) * (13 * xs.length + 13) + n * (bodyBound + 1) ∧
      Invariant 0 final := by
  obtain ⟨cost, final, hs, hbound, hfinal, hinv⟩ :=
    simulation body input tape Invariant bodyBound stable bodyCorrect n xs initial
      hpc hvalue hword hinvariant
  have hhalt : (program body).next input tape final = none := by
    simp [BitRAM.next, hfinal, exit_instruction]
  obtain ⟨hf, hc⟩ := hs.runPriced_ge hhalt
    ((n + 1) * (13 * xs.length + 13) + n * (bodyBound + 1) + 1) (by omega)
  exact ⟨final, hf, hc.trans_le hbound, hinv⟩

end Maxwell.Cost.CountedLoop
