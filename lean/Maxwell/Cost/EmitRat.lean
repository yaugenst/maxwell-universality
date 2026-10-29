import Maxwell.Cost.EmitNat
import Maxwell.Codec.Output

/-! Exact rational-pair serialization by fixed finite Boolean code. The
numerator and denominator magnitudes are already canonical binary words;
the rational pair itself need not be reduced. -/

namespace Maxwell.Cost.EmitRat

def program (numeratorTape denominatorTape : ℕ) : BitRAM := ⟨
  [.output 23] ++
  ((EmitNat.program numeratorTape).code.map (BitRAMInstruction.relocate 1 22)) ++
  ((EmitNat.program denominatorTape).code.map (BitRAMInstruction.relocate 22 43)) ++
  [.halt]⟩

theorem contains_numerator (numeratorTape denominatorTape : ℕ) :
    (program numeratorTape denominatorTape).Contains (EmitNat.program numeratorTape) 1 22 := by
  intro i
  fin_cases i <;> rfl

theorem contains_denominator (numeratorTape denominatorTape : ℕ) :
    (program numeratorTape denominatorTape).Contains (EmitNat.program denominatorTape) 22 43 := by
  intro i
  fin_cases i <;> rfl

def numeratorStart (s : BitRAMState) : BitRAMState :=
  {s with pc := 0, output := s.registers 23 :: s.output}

def denominatorStart (numeratorTape : ℕ) (num : List Bool) (s : BitRAMState) : BitRAMState :=
  {EmitNat.finish numeratorTape num (numeratorStart s) with pc := 0}

def finish (numeratorTape denominatorTape : ℕ) (num den : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {EmitNat.finish denominatorTape den (denominatorStart numeratorTape num s) with pc := 43}

theorem first_block (numeratorTape denominatorTape : ℕ) (input : List Bool)
    (tape : ℕ → Bool) (s : BitRAMState) (hpc : s.pc = 0) :
    PricedSteps ((program numeratorTape denominatorTape).next input tape) 1 s
      ((numeratorStart s).relocate 1) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, program, numeratorStart, hpc,
    BitRAMState.relocate]

theorem denominator_tape (numeratorTape denominatorTape : ℕ)
    (hne : denominatorTape ≠ numeratorTape) (num : List Bool) (s : BitRAMState) :
    (denominatorStart numeratorTape num s).tapes denominatorTape = s.tapes denominatorTape := by
  simp [denominatorStart, EmitNat.finish, EmitNat.payloadStart, EmitNat.rewindStart,
    EmitNat.separatorStart, EmitNat.headerStart, TapeIO.finish, Rewind.finishAt,
    numeratorStart, hne]

/-- The two tape words are read and emitted by actual linked subroutines.
The cost covers the sign, both length headers, both payloads, and returns. -/
theorem steps (numeratorTape denominatorTape : ℕ) (hne : denominatorTape ≠ numeratorTape)
    (input : List Bool) (tape : ℕ → Bool) (num den : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hnum : (s.tapes numeratorTape).Represents num)
    (hden : (s.tapes denominatorTape).Represents den)
    (hnumBlank : (s.tapes numeratorTape).cells ((s.tapes numeratorTape).head - 1) = none)
    (hdenBlank : (s.tapes denominatorTape).cells ((s.tapes denominatorTape).head - 1) = none) :
    PricedSteps ((program numeratorTape denominatorTape).next input tape)
      (16 * (num.length + den.length) + 37) s
      (finish numeratorTape denominatorTape num den s) := by
  have hfirst := first_block numeratorTape denominatorTape input tape s hpc
  have hn := EmitNat.steps numeratorTape input tape num (numeratorStart s) rfl hnum hnumBlank
  have hn' := (contains_numerator numeratorTape denominatorTape).call input tape hn
    (by simp [EmitNat.program, TapeIO.program, Rewind.program,
      BitRAMInstruction.relocate, EmitNat.finish])
  have hd := EmitNat.steps denominatorTape input tape den
    (denominatorStart numeratorTape num s) rfl
    (by simpa only [denominator_tape numeratorTape denominatorTape hne] using hden)
    (by simpa only [denominator_tape numeratorTape denominatorTape hne] using hdenBlank)
  have hd' := (contains_denominator numeratorTape denominatorTape).call input tape hd
    (by simp [EmitNat.program, TapeIO.program, Rewind.program,
      BitRAMInstruction.relocate, EmitNat.finish])
  have hlink : {EmitNat.finish numeratorTape num (numeratorStart s) with pc := 22} =
      (denominatorStart numeratorTape num s).relocate 22 := rfl
  rw [hlink] at hn'
  convert (hfirst.trans hn').trans hd' using 1
  · omega
  · rfl

theorem finish_output (numeratorTape denominatorTape : ℕ) (num den : List Bool)
    (s : BitRAMState) :
    (finish numeratorTape denominatorTape num den s).output =
      (s.registers 23 :: (EmitNat.word num ++ EmitNat.word den)).reverse ++ s.output := by
  simp only [finish, denominatorStart, EmitNat.finish_output, numeratorStart]
  simp [List.reverse_append, List.append_assoc]

theorem finish_pair_output (numeratorTape denominatorTape : ℕ) (q : Codec.RationalPair)
    (s : BitRAMState) (hsign : s.registers 23 = decide (q.numerator < 0)) :
    (finish numeratorTape denominatorTape q.numerator.natAbs.bits q.denominator.bits s).output =
      q.encode.reverse ++ s.output := by
  rw [finish_output, hsign, EmitNat.word_bits, EmitNat.word_bits]
  rfl

theorem run (numeratorTape denominatorTape : ℕ) (hne : denominatorTape ≠ numeratorTape)
    (input : List Bool) (tape : ℕ → Bool) (num den : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hnum : (s.tapes numeratorTape).Represents num)
    (hden : (s.tapes denominatorTape).Represents den)
    (hnumBlank : (s.tapes numeratorTape).cells ((s.tapes numeratorTape).head - 1) = none)
    (hdenBlank : (s.tapes denominatorTape).cells ((s.tapes denominatorTape).head - 1) = none) :
    (runPriced ((program numeratorTape denominatorTape).next input tape)
      (16 * (num.length + den.length) + 38) s).finished =
        some (finish numeratorTape denominatorTape num den s) ∧
    (runPriced ((program numeratorTape denominatorTape).next input tape)
      (16 * (num.length + den.length) + 38) s).instructions =
        16 * (num.length + den.length) + 37 := by
  exact (steps numeratorTape denominatorTape hne input tape num den s hpc
    hnum hden hnumBlank hdenBlank).runPriced
    (by simp [BitRAM.next, program, EmitNat.program, TapeIO.program, Rewind.program,
      finish, BitRAMInstruction.relocate])

end Maxwell.Cost.EmitRat
