import Maxwell.Cost.Machine

namespace Maxwell.Cost

/-- A bit machine has finitely many instructions. The only data literals
are Boolean, and tape heads move one cell at a time. There is no arithmetic
or parser oracle and no input-dependent host-language continuation. -/
inductive BitInstruction where
  | literal (register : ℕ) (value : Bool)
  | readInput (register : ℕ)
  | inputLeft
  | inputRight
  | readWork (register : ℕ)
  | writeWork (register : ℕ)
  | workLeft
  | workRight
  | branch (register yes no : ℕ)
  | jump (target : ℕ)
  | randomBit (register : ℕ)
  | output (register : ℕ)
  | halt
  deriving DecidableEq

structure BitMachine where
  code : List BitInstruction

structure BitState where
  pc : ℕ
  registers : ℕ → Bool
  inputHead : ℤ
  workHead : ℤ
  work : ℤ → Bool
  randomCursor : ℕ
  /-- Reverse output order permits a constant-time emission operation. -/
  output : List Bool

def BitState.initial : BitState :=
  ⟨0, fun _ => false, 0, 0, fun _ => false, 0, []⟩

def BitState.setRegister (s : BitState) (register : ℕ) (v : Bool) : BitState :=
  {s with pc := s.pc + 1, registers := Function.update s.registers register v}

/-- Finite input strings occupy nonnegative input-tape coordinates.
The encoding must include its own delimiters or length representation. -/
def inputBit (input : List Bool) (address : ℤ) : Bool :=
  if address < 0 then false else input[address.toNat]?.getD false

def BitMachine.next (M : BitMachine) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitState) : Option BitState :=
  match M.code[s.pc]? with
  | none | some .halt => none
  | some (.literal register v) => some (s.setRegister register v)
  | some (.readInput register) => some (s.setRegister register (inputBit input s.inputHead))
  | some .inputLeft => some {s with pc := s.pc + 1, inputHead := s.inputHead - 1}
  | some .inputRight => some {s with pc := s.pc + 1, inputHead := s.inputHead + 1}
  | some (.readWork register) => some (s.setRegister register (s.work s.workHead))
  | some (.writeWork register) => some {s with pc := s.pc + 1, work := Function.update s.work s.workHead (s.registers register)}
  | some .workLeft => some {s with pc := s.pc + 1, workHead := s.workHead - 1}
  | some .workRight => some {s with pc := s.pc + 1, workHead := s.workHead + 1}
  | some (.branch register yes no) =>
      some {s with pc := if s.registers register then yes else no}
  | some (.jump target) => some {s with pc := target}
  | some (.randomBit register) =>
      some {s.setRegister register (randomTape s.randomCursor) with
        randomCursor := s.randomCursor + 1}
  | some (.output register) => some {s with pc := s.pc + 1, output := s.registers register :: s.output}

def BitMachine.run (M : BitMachine) (input : List Bool)
    (randomTape : ℕ → Bool) (fuel : ℕ) : CappedResult BitState :=
  runCapped (M.next input randomTape) fuel BitState.initial

theorem BitMachine.run_all_inputs_le (M : BitMachine) (input : List Bool)
    (randomTape : ℕ → Bool) (fuel : ℕ) :
    (M.run input randomTape fuel).instructions ≤ fuel :=
  runCapped_le _ _ _

/-- Every output bit and every random draw costs an actual machine step. -/
theorem BitMachine.next_output_random_bound (M : BitMachine) (input : List Bool)
    (randomTape : ℕ → Bool) (s t : BitState)
    (h : M.next input randomTape s = some t) :
    t.output.length + t.randomCursor ≤ s.output.length + s.randomCursor + 1 := by
  unfold BitMachine.next at h
  cases hc : M.code[s.pc]? with
  | none => simp [hc] at h
  | some instruction =>
    cases instruction <;> simp only [hc, Option.some.injEq, reduceCtorEq] at h <;>
      try contradiction
    all_goals subst t
    all_goals simp [BitState.setRegister]
    all_goals omega

/-- Output and randomness bounds follow from the operational run, including
on inputs violating all promised numerical conditions. -/
theorem BitMachine.terminates_output_random_bound (M : BitMachine)
    (input : List Bool) (randomTape : ℕ → Bool) {n : ℕ} {s t : BitState}
    (h : Terminates (M.next input randomTape) n s t) :
    t.output.length + t.randomCursor ≤ s.output.length + s.randomCursor + n := by
  induction h with
  | halt s h => omega
  | @step n s t u h rest ih =>
    have hstep := M.next_output_random_bound input randomTape s t h
    omega

theorem BitMachine.run_output_random_bound (M : BitMachine)
    (input : List Bool) (randomTape : ℕ → Bool) (fuel : ℕ) (output : BitState)
    (h : (M.run input randomTape fuel).finished = some output) :
    output.output.length + output.randomCursor ≤ fuel := by
  have ht := runCapped_sound (M.next input randomTape) fuel h
  have hb := M.terminates_output_random_bound input randomTape ht
  simp only [BitState.initial, List.length_nil, zero_add] at hb
  exact hb.trans (M.run_all_inputs_le input randomTape fuel)

end Maxwell.Cost
