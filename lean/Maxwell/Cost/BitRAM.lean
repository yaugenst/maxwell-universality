import Maxwell.Cost.BitMachine

namespace Maxwell.Cost

/-- A priced transition costs one plus `extra` bit operations. The cost is
not supplied by an algorithm: each instruction's semantics determines it. -/
structure PricedStep (σ : Type) where
  state : σ
  extra : ℕ

inductive MicroState (σ : Type) where
  | ready : σ → MicroState σ
  /-- `remaining+1` unit operations must elapse before another instruction. -/
  | delay : ℕ → σ → MicroState σ

def microNext {σ : Type} (next : σ → Option (PricedStep σ)) :
    MicroState σ → Option (MicroState σ)
  | .delay 0 state => some (.ready state)
  | .delay (n + 1) state => some (.delay n state)
  | .ready state => match next state with
      | none => none
      | some ⟨state', 0⟩ => some (.ready state')
      | some ⟨state', n + 1⟩ => some (.delay n state')

def MicroState.completed {σ : Type} : MicroState σ → Option σ
  | .ready s => some s
  | .delay _ _ => none

def runPriced {σ : Type} (next : σ → Option (PricedStep σ))
    (fuel : ℕ) (initial : σ) : CappedResult σ :=
  let result := runCapped (microNext next) fuel (.ready initial)
  ⟨result.finished.bind MicroState.completed, result.instructions⟩

theorem runPriced_le {σ : Type} (next : σ → Option (PricedStep σ))
    (fuel : ℕ) (initial : σ) : (runPriced next fuel initial).instructions ≤ fuel := by
  exact runCapped_le (microNext next) fuel (.ready initial)

/-- Exact arithmetic of word addresses is represented by their explicit
binary strings. There is no unit-cost unbounded integer arithmetic. -/
def addressValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * addressValue bs

inductive BitRAMInstruction where
  | literal (register : ℕ) (value : Bool)
  | bitXor (dst left right : ℕ)
  | bitAnd (dst left right : ℕ)
  | bitNot (dst src : ℕ)
  | readSequential (register : ℕ)
  | inputLeft
  | inputRight
  | addressPeek (register : ℕ)
  | addressIsEmpty (register : ℕ)
  | readTape (tape valueRegister presentRegister : ℕ)
  | writeTape (tape valueRegister : ℕ)
  | eraseTape (tape : ℕ)
  | tapeLeft (tape : ℕ)
  | tapeRight (tape : ℕ)
  | addressPush (register : ℕ)
  | addressPop
  | addressClear
  | readInput (register : ℕ)
  | readMemory (register : ℕ)
  | writeMemory (register : ℕ)
  | branch (register yes no : ℕ)
  | jump (target : ℕ)
  | randomBit (register : ℕ)
  | output (register : ℕ)
  | halt
  deriving DecidableEq

structure BitRAM where
  code : List BitRAMInstruction

/-- A sequential Boolean tape has a distinct blank symbol and unit head
moves. Each tape identifier is a fixed literal in the finite program. -/
structure BitTape where
  head : ℤ
  cells : ℤ → Option Bool

def BitTape.blank : BitTape := ⟨0, fun _ => none⟩

def BitTape.read (tape : BitTape) : Option Bool := tape.cells tape.head

def BitTape.write (tape : BitTape) (symbol : Option Bool) : BitTape :=
  {tape with cells := Function.update tape.cells tape.head symbol}

structure BitRAMState where
  pc : ℕ
  registers : ℕ → Bool
  address : List Bool
  inputHead : ℤ
  tapes : ℕ → BitTape
  memory : ℕ → Bool
  randomCursor : ℕ
  output : List Bool

def BitRAMState.initial : BitRAMState :=
  ⟨0, fun _ => false, [], 0, fun _ => BitTape.blank, fun _ => false, 0, []⟩

def BitRAMState.setRegister (s : BitRAMState) (register : ℕ) (v : Bool) : BitRAMState :=
  {s with pc := s.pc + 1, registers := Function.update s.registers register v}

def BitRAMState.setTape (s : BitRAMState) (tape : ℕ) (value : BitTape) : BitRAMState :=
  {s with pc := s.pc + 1, tapes := Function.update s.tapes tape value}

/-- Random-access bit reads and writes cost the full binary address length
plus the accessed bit. All other operations affect one Boolean symbol or
one finite-control register and cost one. Address strings are constructed
by separately charged pushes; constants in the finite code are Boolean. -/
def BitRAM.next (M : BitRAM) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitRAMState) : Option (PricedStep BitRAMState) :=
  match M.code[s.pc]? with
  | none | some .halt => none
  | some (.literal register v) => some ⟨s.setRegister register v, 0⟩
  | some (.bitXor dst left right) => some ⟨s.setRegister dst (xor (s.registers left) (s.registers right)), 0⟩
  | some (.bitAnd dst left right) => some ⟨s.setRegister dst (s.registers left && s.registers right), 0⟩
  | some (.bitNot dst src) => some ⟨s.setRegister dst (!s.registers src), 0⟩
  | some (.readSequential register) => some ⟨s.setRegister register (inputBit input s.inputHead), 0⟩
  | some .inputLeft => some ⟨{s with pc := s.pc + 1, inputHead := s.inputHead - 1}, 0⟩
  | some .inputRight => some ⟨{s with pc := s.pc + 1, inputHead := s.inputHead + 1}, 0⟩
  | some (.addressPeek register) => some ⟨s.setRegister register (s.address.headD false), 0⟩
  | some (.addressIsEmpty register) => some ⟨s.setRegister register s.address.isEmpty, 0⟩
  | some (.readTape tape valueRegister presentRegister) =>
      some ⟨{s.setRegister valueRegister ((s.tapes tape).read.getD false) with
        registers := Function.update (Function.update s.registers valueRegister
          ((s.tapes tape).read.getD false)) presentRegister ((s.tapes tape).read.isSome)}, 1⟩
  | some (.writeTape tape valueRegister) =>
      some ⟨s.setTape tape ((s.tapes tape).write (some (s.registers valueRegister))), 0⟩
  | some (.eraseTape tape) => some ⟨s.setTape tape ((s.tapes tape).write none), 0⟩
  | some (.tapeLeft tape) => some ⟨s.setTape tape {s.tapes tape with head := (s.tapes tape).head - 1}, 0⟩
  | some (.tapeRight tape) => some ⟨s.setTape tape {s.tapes tape with head := (s.tapes tape).head + 1}, 0⟩
  | some (.addressPush register) =>
      some ⟨{s with pc := s.pc + 1, address := s.registers register :: s.address}, 0⟩
  | some .addressPop => some ⟨{s with pc := s.pc + 1, address := s.address.tail}, 0⟩
  | some .addressClear => some ⟨{s with pc := s.pc + 1, address := []}, 0⟩
  | some (.readInput register) =>
      some ⟨s.setRegister register (input[addressValue s.address]?.getD false), s.address.length⟩
  | some (.readMemory register) =>
      some ⟨s.setRegister register (s.memory (addressValue s.address)), s.address.length⟩
  | some (.writeMemory register) =>
      some ⟨{s with pc := s.pc + 1, memory := Function.update s.memory (addressValue s.address) (s.registers register)}, s.address.length⟩
  | some (.branch register yes no) =>
      some ⟨{s with pc := if s.registers register then yes else no}, 0⟩
  | some (.jump target) => some ⟨{s with pc := target}, 0⟩
  | some (.randomBit register) =>
      some ⟨{s.setRegister register (randomTape s.randomCursor) with
        randomCursor := s.randomCursor + 1}, 0⟩
  | some (.output register) =>
      some ⟨{s with pc := s.pc + 1, output := s.registers register :: s.output}, 0⟩

def BitRAM.run (M : BitRAM) (input : List Bool) (randomTape : ℕ → Bool)
    (fuel : ℕ) : CappedResult BitRAMState :=
  runPriced (M.next input randomTape) fuel BitRAMState.initial

theorem BitRAM.run_all_inputs_le (M : BitRAM) (input : List Bool)
    (randomTape : ℕ → Bool) (fuel : ℕ) :
    (M.run input randomTape fuel).instructions ≤ fuel := runPriced_le _ _ _

/-- A bit-memory access charges all address bits on every execution. -/
theorem BitRAM.readMemory_price (M : BitRAM) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitRAMState) (register : ℕ)
    (h : M.code[s.pc]? = some (.readMemory register)) :
    M.next input randomTape s =
      some ⟨s.setRegister register (s.memory (addressValue s.address)), s.address.length⟩ := by
  simp [BitRAM.next, h]

/-- A successful result must come from an actual terminated, fully charged
micro-execution; no return can occur halfway through an address charge. -/
theorem runPriced_sound {σ : Type} (next : σ → Option (PricedStep σ))
    (fuel : ℕ) (initial final : σ)
    (h : (runPriced next fuel initial).finished = some final) :
    Terminates (microNext next) (runPriced next fuel initial).instructions
      (.ready initial) (.ready final) := by
  unfold runPriced at h ⊢
  cases hr : (runCapped (microNext next) fuel (.ready initial)).finished with
  | none => simp [hr] at h
  | some state =>
    cases state with
    | delay n state => simp [hr, MicroState.completed] at h
    | ready state =>
      simp [hr, MicroState.completed] at h
      subst state
      exact runCapped_sound (microNext next) fuel hr

/-- A concrete finite program draws and emits one bit, with both charged. -/
def randomBitEmitter : BitRAM :=
  ⟨[.randomBit 0, .output 0, .halt]⟩

theorem randomBitEmitter_cost (input : List Bool) (tape : ℕ → Bool) :
    (randomBitEmitter.run input tape 3).instructions = 2 := by
  simp [BitRAM.run, runPriced, runCapped, microNext, BitRAM.next,
    randomBitEmitter, BitRAMState.initial, BitRAMState.setRegister]

theorem randomBitEmitter_output (input : List Bool) (tape : ℕ → Bool) :
    (randomBitEmitter.run input tape 3).finished.map BitRAMState.output = some [tape 0] := by
  simp [BitRAM.run, runPriced, runCapped, microNext, BitRAM.next,
    randomBitEmitter, BitRAMState.initial, BitRAMState.setRegister, MicroState.completed]

/-- One primitive changes emitted-bit count plus consumed-random-bit count
by at most one. Address operations cannot create either kind of bit. -/
theorem BitRAM.next_output_random_bound (M : BitRAM) (input : List Bool)
    (tape : ℕ → Bool) (s : BitRAMState) (step : PricedStep BitRAMState)
    (h : M.next input tape s = some step) :
    step.state.output.length + step.state.randomCursor ≤
      s.output.length + s.randomCursor + 1 := by
  unfold BitRAM.next at h
  cases hc : M.code[s.pc]? with
  | none => simp [hc] at h
  | some instruction =>
    cases instruction <;> simp only [hc, Option.some.injEq, reduceCtorEq] at h <;>
      try contradiction
    all_goals subst step
    all_goals simp [BitRAMState.setRegister, BitRAMState.setTape]
    all_goals omega

def MicroState.state {σ : Type} : MicroState σ → σ
  | .ready s => s
  | .delay _ s => s

theorem BitRAM.micro_output_random_bound (M : BitRAM) (input : List Bool)
    (tape : ℕ → Bool) (s t : MicroState BitRAMState)
    (h : microNext (M.next input tape) s = some t) :
    t.state.output.length + t.state.randomCursor ≤
      s.state.output.length + s.state.randomCursor + 1 := by
  cases s with
  | delay n state =>
    cases n <;> simp only [microNext, Option.some.injEq] at h <;>
      subst t <;> simp [MicroState.state]
  | ready state =>
    cases hc : M.next input tape state with
    | none => simp [microNext, hc] at h
    | some step =>
      have hb := M.next_output_random_bound input tape state step hc
      rcases step with ⟨target, extra⟩
      cases extra <;> simp only [microNext, hc, Option.some.injEq] at h <;>
        subst t <;> exact hb

theorem terminates_potential_bound {σ : Type} (next : σ → Option σ)
    (potential : σ → ℕ)
    (stepBound : ∀ s t, next s = some t → potential t ≤ potential s + 1)
    {n : ℕ} {s t : σ} (h : Terminates next n s t) :
    potential t ≤ potential s + n := by
  induction h with
  | halt s h => omega
  | @step n s t u h rest ih =>
    have hs := stepBound s t h
    omega

theorem BitRAM.run_output_random_bound (M : BitRAM) (input : List Bool)
    (tape : ℕ → Bool) (fuel : ℕ) (output : BitRAMState)
    (h : (M.run input tape fuel).finished = some output) :
    output.output.length + output.randomCursor ≤ fuel := by
  have ht := runPriced_sound (M.next input tape) fuel BitRAMState.initial output h
  have hb := terminates_potential_bound (microNext (M.next input tape))
    (fun s => s.state.output.length + s.state.randomCursor)
    (M.micro_output_random_bound input tape) ht
  simp only [MicroState.state, BitRAMState.initial, List.length_nil, zero_add] at hb
  exact hb.trans (M.run_all_inputs_le input tape fuel)

end Maxwell.Cost
