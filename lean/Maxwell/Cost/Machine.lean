import Maxwell.Cost.Model

/-!
# Uniform finite-code Real RAM and a genuine time cap

Unlike a free-language specification, `Machine` contains a finite list of
instructions and rational literal constants. Input-dependent arithmetic
and control flow are performed by the transition relation. In particular,
there is no instruction accepting an arbitrary function of the whole input.
The supplied tape records random bits; advancing it costs one instruction.
-/
namespace Maxwell.Cost

inductive RAMInstruction where
  | literal (dst : ℕ) (value : ℚ)
  | copy (dst src : ℕ)
  | add (dst left right : ℕ)
  | multiply (dst left right : ℕ)
  | divide (dst left right : ℕ)
  | input (dst addressRegister : ℕ)
  | inputIndex (dst addressRegister : ℕ)
  | load (dst addressRegister : ℕ)
  | store (addressRegister src : ℕ)
  | loadIndex (dst addressRegister : ℕ)
  | storeIndex (addressRegister src : ℕ)
  | indexLiteral (dst value : ℕ)
  | indexCopy (dst src : ℕ)
  | indexAdd (dst left right : ℕ)
  | indexSubtract (dst left right : ℕ)
  | branchLE (left right yes no : ℕ)
  | branchIndexLE (left right yes no : ℕ)
  | jump (target : ℕ)
  | randomBit (dst : ℕ)
  | output (src : ℕ)
  | outputIndex (src : ℕ)
  | halt
  deriving DecidableEq

structure Machine where
  code : List RAMInstruction

/-- Sparse input separates real coefficients from machine-index words.
Both tapes are read by charged instructions; indices are never obtained
by an uncharged conversion of arbitrary real coefficients. -/
structure RAMInput where
  words : ℕ → ℝ
  indices : ℕ → ℕ

structure RAMState where
  pc : ℕ
  words : ℕ → ℝ
  indices : ℕ → ℕ
  randomCursor : ℕ
  output : List ℝ
  indexOutput : List ℕ

noncomputable def RAMState.initial : RAMState :=
  ⟨0, fun _ => 0, fun _ => 0, 0, [], []⟩

noncomputable def RAMState.setWord (s : RAMState) (i : ℕ) (v : ℝ) : RAMState :=
  {s with pc := s.pc + 1, words := Function.update s.words i v}

def RAMState.setIndex (s : RAMState) (i v : ℕ) : RAMState :=
  {s with pc := s.pc + 1, indices := Function.update s.indices i v}

/-- One actual RAM instruction, or `none` precisely at a halted machine.
Out-of-code control is halted, so the semantics also covers small programs. -/
noncomputable def Machine.next (M : Machine) (input : RAMInput)
    (randomTape : ℕ → Bool) (s : RAMState) : Option RAMState :=
  match M.code[s.pc]? with
  | none | some .halt => none
  | some (.literal dst v) => some (s.setWord dst v)
  | some (.copy dst src) => some (s.setWord dst (s.words src))
  | some (.add dst a b) => some (s.setWord dst (s.words a + s.words b))
  | some (.multiply dst a b) => some (s.setWord dst (s.words a * s.words b))
  | some (.divide dst a b) => some (s.setWord dst (s.words a / s.words b))
  | some (.input dst address) => some (s.setWord dst (input.words (s.indices address)))
  | some (.inputIndex dst address) => some (s.setIndex dst (input.indices (s.indices address)))
  | some (.load dst address) => some (s.setWord dst (s.words (s.indices address)))
  | some (.store address src) => some (s.setWord (s.indices address) (s.words src))
  | some (.loadIndex dst address) => some (s.setIndex dst (s.indices (s.indices address)))
  | some (.storeIndex address src) => some (s.setIndex (s.indices address) (s.indices src))
  | some (.indexLiteral dst v) => some (s.setIndex dst v)
  | some (.indexCopy dst src) => some (s.setIndex dst (s.indices src))
  | some (.indexAdd dst a b) => some (s.setIndex dst (s.indices a + s.indices b))
  | some (.indexSubtract dst a b) => some (s.setIndex dst (s.indices a - s.indices b))
  | some (.branchLE a b yes no) =>
      some {s with pc := if s.words a ≤ s.words b then yes else no}
  | some (.branchIndexLE a b yes no) =>
      some {s with pc := if s.indices a ≤ s.indices b then yes else no}
  | some (.jump target) => some {s with pc := target}
  | some (.randomBit dst) =>
      some {s.setWord dst (if randomTape s.randomCursor then 1 else 0) with
        randomCursor := s.randomCursor + 1}
  | some (.output src) => some {s with pc := s.pc + 1, output := s.words src :: s.output}
  | some (.outputIndex src) =>
      some {s with pc := s.pc + 1, indexOutput := s.indices src :: s.indexOutput}

structure CappedResult (σ : Type) where
  /-- `some` occurs only after the machine has actually halted. -/
  finished : Option σ
  instructions : ℕ

/-- A cap operates on machine transitions, including on bad or singular
inputs. At zero fuel no further transition is evaluated. -/
def runCapped {σ : Type} (next : σ → Option σ) : ℕ → σ → CappedResult σ
  | 0, _ => ⟨none, 0⟩
  | fuel + 1, state =>
      match next state with
      | none => ⟨some state, 0⟩
      | some state' =>
          let rest := runCapped next fuel state'
          ⟨rest.finished, rest.instructions + 1⟩

theorem runCapped_le {σ : Type} (next : σ → Option σ) (fuel : ℕ) (state : σ) :
    (runCapped next fuel state).instructions ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [runCapped]
  | succ fuel ih =>
    simp only [runCapped]
    split
    · simp
    · exact Nat.add_le_add_right (ih _) 1

/-- The execution relation records actual transition count and final halt. -/
inductive Terminates {σ : Type} (next : σ → Option σ) : ℕ → σ → σ → Prop where
  | halt (s : σ) (h : next s = none) : Terminates next 0 s s
  | step {n : ℕ} {s t u : σ} (h : next s = some t)
      (rest : Terminates next n t u) : Terminates next (n + 1) s u

/-- A good-instance termination theorem transfers to the same machine run
with a cap. The additional unit allows observing its final halt. -/
theorem runCapped_of_terminates {σ : Type} (next : σ → Option σ)
    {n : ℕ} {start stop : σ} (h : Terminates next n start stop) :
    (runCapped next (n + 1) start).finished = some stop ∧
      (runCapped next (n + 1) start).instructions = n := by
  induction h with
  | halt s h => simp [runCapped, h]
  | @step n s t u h rest ih =>
    rw [runCapped, h]
    change (runCapped next (n + 1) t).finished = some u ∧
      (runCapped next (n + 1) t).instructions + 1 = n + 1
    · exact ⟨ih.1, congrArg (fun k => k + 1) ih.2⟩

/-- Every successful capped return is an actual terminating execution;
there is no fabricated output on exhaustion of the time budget. -/
theorem runCapped_sound {σ : Type} (next : σ → Option σ) (fuel : ℕ)
    {start stop : σ} (h : (runCapped next fuel start).finished = some stop) :
    Terminates next (runCapped next fuel start).instructions start stop := by
  induction fuel generalizing start with
  | zero => simp [runCapped] at h
  | succ fuel ih =>
    cases hn : next start with
    | none =>
      simp [runCapped, hn] at h
      subst stop
      simpa [runCapped, hn] using Terminates.halt start hn
    | some t =>
      have hrest : (runCapped next fuel t).finished = some stop := by
        simpa [runCapped, hn] using h
      simpa [runCapped, hn] using Terminates.step hn (ih hrest)

noncomputable def Machine.run (M : Machine) (input : RAMInput)
    (randomTape : ℕ → Bool) (fuel : ℕ) : CappedResult RAMState :=
  runCapped (M.next input randomTape) fuel RAMState.initial

theorem Machine.run_all_inputs_le (M : Machine) (input : RAMInput)
    (randomTape : ℕ → Bool) (fuel : ℕ) :
    (M.run input randomTape fuel).instructions ≤ fuel :=
  runCapped_le _ _ _

/-- Fixed preprocessing is a finite prefix of the same execution cost,
not free advice. For any fixed terminated search its actual cost is constant. -/
theorem fixed_preprocessing_charged {σ : Type} (next : σ → Option σ)
    {steps : ℕ} {initial selected : σ} (search : Terminates next steps initial selected)
    (inputCost : ℕ) :
    (runCapped next (steps + 1) initial).instructions + inputCost = steps + inputCost := by
  rw [(runCapped_of_terminates next search).2]

end Maxwell.Cost
