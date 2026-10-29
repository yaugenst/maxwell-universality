import Maxwell.Cost.Execution

set_option linter.unusedSimpArgs false
namespace Maxwell.Cost

@[simp] theorem setRegister_pc (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).pc = s.pc + 1 := rfl
@[simp] theorem setRegister_registers (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).registers = Function.update s.registers r b := rfl
@[simp] theorem setRegister_tapes (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).tapes = s.tapes := rfl
@[simp] theorem setTape_pc (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).pc = s.pc + 1 := rfl
@[simp] theorem setTape_registers (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).registers = s.registers := rfl
@[simp] theorem setTape_tapes (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).tapes = Function.update s.tapes r t := rfl

@[simp] theorem setRegister_address (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).address = s.address := rfl
@[simp] theorem setRegister_inputHead (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).inputHead = s.inputHead := rfl
@[simp] theorem setRegister_memory (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).memory = s.memory := rfl
@[simp] theorem setRegister_randomCursor (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).randomCursor = s.randomCursor := rfl
@[simp] theorem setRegister_output (s : BitRAMState) (r : ℕ) (b : Bool) :
    (s.setRegister r b).output = s.output := rfl
@[simp] theorem setTape_address (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).address = s.address := rfl
@[simp] theorem setTape_inputHead (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).inputHead = s.inputHead := rfl
@[simp] theorem setTape_memory (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).memory = s.memory := rfl
@[simp] theorem setTape_randomCursor (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).randomCursor = s.randomCursor := rfl
@[simp] theorem setTape_output (s : BitRAMState) (r : ℕ) (t : BitTape) :
    (s.setTape r t).output = s.output := rfl

/-- Three input bits are in Boolean registers 0,1,2. The program leaves the
sum bit in register 4 and carry in register 2. Every gate is actual finite
BitRAM code, not a host-language arithmetic continuation. -/
def fullAdder : BitRAM := ⟨[
  .bitXor 3 0 1,
  .bitXor 4 3 2,
  .bitAnd 5 0 1,
  .bitAnd 6 3 2,
  .bitXor 2 5 6,
  .halt]⟩

def fullAdderFinal (s : BitRAMState) : BitRAMState :=
  let s := s.setRegister 3 (xor (s.registers 0) (s.registers 1))
  let s := s.setRegister 4 (xor (s.registers 3) (s.registers 2))
  let s := s.setRegister 5 (s.registers 0 && s.registers 1)
  let s := s.setRegister 6 (s.registers 3 && s.registers 2)
  s.setRegister 2 (xor (s.registers 5) (s.registers 6))

theorem fullAdder_run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    runPriced (fullAdder.next input tape) 6 s = ⟨some (fullAdderFinal s), 5⟩ := by
  simp [runPriced, runCapped, microNext, fullAdder, BitRAM.next,
    fullAdderFinal, BitRAMState.setRegister, hpc, MicroState.completed]

theorem fullAdder_binary_value (a b carry : Bool) :
    (xor (xor a b) carry).toNat +
      2 * (xor (a && b) ((xor a b) && carry)).toNat =
        a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

theorem fullAdderFinal_value (s : BitRAMState) :
    ((fullAdderFinal s).registers 4).toNat + 2 * ((fullAdderFinal s).registers 2).toNat =
      (s.registers 0).toNat + (s.registers 1).toNat + (s.registers 2).toNat := by
  simp [fullAdderFinal, BitRAMState.setRegister]
  simpa using fullAdder_binary_value (s.registers 0) (s.registers 1) (s.registers 2)

/-- A concrete finite-code arithmetic routine has both exact binary-value
correctness and five charged Boolean operations. -/
theorem fullAdder_correct (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    ∃ final, (runPriced (fullAdder.next input tape) 6 s).finished = some final ∧
      (runPriced (fullAdder.next input tape) 6 s).instructions = 5 ∧
      (final.registers 4).toNat + 2 * (final.registers 2).toNat =
        (s.registers 0).toNat + (s.registers 1).toNat + (s.registers 2).toNat := by
  refine ⟨fullAdderFinal s, ?_, ?_, fullAdderFinal_value s⟩ <;>
    rw [fullAdder_run input tape s hpc]

/-- Uniform ripple-addition control. Operands are little-endian bit strings
on tapes 0 and 1, terminated by blank cells. Tape 2 receives the result.
The carry starts in register 2; registers 0 through 11 are scratch.
The final extra carry, if present, is emitted before halting. -/
def rippleAdder : BitRAM := ⟨[
  .readTape 0 0 7,
  .readTape 1 1 8,
  .bitNot 9 7,
  .bitNot 10 8,
  .bitAnd 11 9 10,
  .branch 11 6 7,
  .branch 2 7 17,
  .bitXor 3 0 1,
  .bitXor 4 3 2,
  .bitAnd 5 0 1,
  .bitAnd 6 3 2,
  .bitXor 2 5 6,
  .writeTape 2 4,
  .tapeRight 0,
  .tapeRight 1,
  .tapeRight 2,
  .jump 0,
  .halt]⟩

/-- The binary recurrence implemented by the fixed ripple program. -/
def addBits (carry : Bool) : List Bool → List Bool → List Bool
  | [], [] => if carry then [true] else []
  | a :: as, [] => xor (xor a false) carry ::
      addBits (xor (a && false) ((xor a false) && carry)) as []
  | [], b :: bs => xor (xor false b) carry ::
      addBits (xor (false && b) ((xor false b) && carry)) [] bs
  | a :: as, b :: bs => xor (xor a b) carry ::
      addBits (xor (a && b) ((xor a b) && carry)) as bs
termination_by xs ys => xs.length + ys.length

theorem addBits_value (carry : Bool) (as bs : List Bool) :
    addressValue (addBits carry as bs) = addressValue as + addressValue bs + carry.toNat := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [addBits, addressValue]
    | cons b bs ih =>
      rw [addBits]
      simp only [addressValue]
      rw [ih]
      have h := fullAdder_binary_value false b carry
      simp only [addressValue] at ⊢
      simp only [Bool.false_and, Bool.false_xor, Bool.toNat_false] at h ⊢
      omega
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [addBits]
      simp only [addressValue]
      rw [ih]
      have h := fullAdder_binary_value a false carry
      simp only [addressValue] at ⊢
      simp only [Bool.and_false, Bool.xor_false, Bool.toNat_false] at h ⊢
      omega
    | cons b bs =>
      rw [addBits]
      simp only [addressValue]
      rw [ih]
      have h := fullAdder_binary_value a b carry
      omega

theorem addBits_length_le (carry : Bool) (as bs : List Bool) :
    (addBits carry as bs).length ≤ max as.length bs.length + 1 := by
  induction as generalizing bs carry with
  | nil =>
    induction bs generalizing carry with
    | nil => cases carry <;> simp [addBits]
    | cons b bs ih =>
      simp only [addBits, List.length_cons, List.length_nil, Nat.zero_max]
      exact Nat.add_le_add_right (ih _) 1
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [addBits, List.length_cons, List.length_nil, Nat.max_zero]
      simpa only [List.length_nil, Nat.max_zero] using Nat.add_le_add_right (ih _ []) 1
    | cons b bs =>
      simp only [addBits, List.length_cons, max_add_add_right]
      exact Nat.add_le_add_right (ih _ _) 1

/-- Exact finite sequence of tape-cell writes, used only to describe the
observable effect of executed write-and-move instructions. -/
def writeCells (cells : ℤ → Option Bool) (start : ℤ) : List Bool → ℤ → Option Bool
  | [] => cells
  | b :: bs => writeCells (Function.update cells start (some b)) (start + 1) bs

theorem writeCells_append (cells : ℤ → Option Bool) (start : ℤ) (xs ys : List Bool) :
    writeCells (writeCells cells start xs) (start + xs.length) ys =
      writeCells cells start (xs ++ ys) := by
  induction xs generalizing cells start with
  | nil => simp [writeCells]
  | cons x xs ih =>
    simp only [writeCells, List.length_cons, List.cons_append, Nat.cast_add, Nat.cast_one]
    simpa [add_assoc, add_comm, add_left_comm] using
      ih (Function.update cells start (some x)) (start + 1)

theorem writeCells_preserves_left (cells : ℤ → Option Bool) (start point : ℤ)
    (xs : List Bool) (h : point < start) : writeCells cells start xs point = cells point := by
  induction xs generalizing cells start with
  | nil => rfl
  | cons x xs ih =>
    rw [writeCells, ih _ _ (by omega)]
    simp [Function.update, ne_of_lt h]

theorem writeCells_read (cells : ℤ → Option Bool) (start : ℤ)
    (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    writeCells cells start xs (start + i) = xs[i]? := by
  induction xs generalizing cells start i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [writeCells, writeCells_preserves_left _ _ _ _ (by omega)]
      simp [Function.update]
    | succ i =>
      have hii : i < xs.length := by simpa using hi
      have heq : start + ((i + 1 : ℕ) : ℤ) = (start + 1) + i := by push_cast; ring
      rw [writeCells, heq, ih _ _ i hii]
      simp

structure TapeWrites (before after : BitTape) (bits : List Bool) : Prop where
  head : after.head = before.head + bits.length
  cells : after.cells = writeCells before.cells before.head bits

theorem TapeWrites.refl (tape : BitTape) : TapeWrites tape tape [] := by
  constructor <;> simp [writeCells]

theorem TapeWrites.trans {before middle after : BitTape} {xs ys : List Bool}
    (hx : TapeWrites before middle xs) (hy : TapeWrites middle after ys) :
    TapeWrites before after (xs ++ ys) := by
  constructor
  · rw [hy.head, hx.head, List.length_append, Nat.cast_add]
    ring
  · rw [hy.cells, hx.cells, hx.head, writeCells_append]

theorem TapeWrites.read {before after : BitTape} {bits : List Bool}
    (h : TapeWrites before after bits) (i : ℕ) (hi : i < bits.length) :
    after.cells (before.head + i) = bits[i]? := by
  rw [h.cells]
  exact writeCells_read _ _ _ _ hi

def readTapeState (s : BitRAMState) (tape valueRegister presentRegister : ℕ) : BitRAMState :=
  {s with pc := s.pc + 1, registers := Function.update (Function.update s.registers valueRegister
      ((s.tapes tape).read.getD false)) presentRegister ((s.tapes tape).read.isSome)}

def rippleLoaded (s : BitRAMState) : BitRAMState :=
  let s := readTapeState s 0 0 7
  let s := readTapeState s 1 1 8
  let s := s.setRegister 9 (!s.registers 7)
  let s := s.setRegister 10 (!s.registers 8)
  s.setRegister 11 (s.registers 9 && s.registers 10)

def rippleRound (s : BitRAMState) : BitRAMState :=
  let s := fullAdderFinal {(rippleLoaded s) with pc := 7}
  let s := s.setTape 2 ((s.tapes 2).write (some (s.registers 4)))
  let s := s.setTape 0 {s.tapes 0 with head := (s.tapes 0).head + 1}
  let s := s.setTape 1 {s.tapes 1 with head := (s.tapes 1).head + 1}
  let s := s.setTape 2 {s.tapes 2 with head := (s.tapes 2).head + 1}
  {s with pc := 0}

def rippleStopped (s : BitRAMState) : BitRAMState := {(rippleLoaded s) with pc := 17}

def rippleNonempty (s : BitRAMState) : Bool :=
  (s.tapes 0).read.isSome || (s.tapes 1).read.isSome

def rippleRoundInstructions (s : BitRAMState) : ℕ := if rippleNonempty s then 16 else 17

def rippleRoundCost (s : BitRAMState) : ℕ := if rippleNonempty s then 18 else 19

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem rippleRound_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (active : rippleNonempty s = true ∨ s.registers 2 = true) :
    executeInstructions (rippleAdder.next input tape) (rippleRoundInstructions s) s =
      some (rippleRound s, rippleRoundCost s) := by
  cases ha : (s.tapes 0).read <;> cases hb : (s.tapes 1).read <;>
    cases hc : s.registers 2 <;>
    simp [rippleNonempty, ha, hb, hc] at active
  all_goals simp (config := { maxSteps := 400000 }) [rippleRoundInstructions, rippleRoundCost,
    rippleNonempty, ha, hb, executeInstructions, rippleAdder, BitRAM.next,
    rippleRound, rippleLoaded, readTapeState, fullAdderFinal, BitTape.write, hpc, hc]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem rippleStop_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (ha : (s.tapes 0).read = none) (hb : (s.tapes 1).read = none)
    (hc : s.registers 2 = false) :
    executeInstructions (rippleAdder.next input tape) 7 s = some (rippleStopped s, 9) := by
  simp [executeInstructions, rippleAdder, BitRAM.next, rippleStopped, rippleLoaded,
    readTapeState, BitRAMState.setRegister, hpc, ha, hb, hc]

theorem rippleStopped_halt (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) :
    rippleAdder.next input tape (rippleStopped s) = none := by
  simp [rippleAdder, BitRAM.next, rippleStopped]

def TapeRepresents (tape : BitTape) (bits : List Bool) : Prop :=
  ∀ k : ℕ, tape.cells (tape.head + k) = bits[k]?

theorem TapeRepresents.read {tape : BitTape} {bits : List Bool}
    (h : TapeRepresents tape bits) : tape.read = bits.head? := by
  simpa [BitTape.read, List.head?_eq_getElem?] using h 0

theorem TapeRepresents.moveRight {tape : BitTape} {bits : List Bool}
    (h : TapeRepresents tape bits) :
    TapeRepresents {tape with head := tape.head + 1} bits.tail := by
  intro k
  have hh := h (k + 1)
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hh

theorem rippleRound_tape0 (s : BitRAMState) :
    (rippleRound s).tapes 0 = {s.tapes 0 with head := (s.tapes 0).head + 1} := by
  simp [rippleRound, fullAdderFinal, rippleLoaded, readTapeState,
    BitRAMState.setRegister, BitRAMState.setTape]

theorem rippleRound_tape1 (s : BitRAMState) :
    (rippleRound s).tapes 1 = {s.tapes 1 with head := (s.tapes 1).head + 1} := by
  simp [rippleRound, fullAdderFinal, rippleLoaded, readTapeState,
    BitRAMState.setRegister, BitRAMState.setTape]

def rippleSumBit (s : BitRAMState) : Bool :=
  xor (xor ((s.tapes 0).read.getD false) ((s.tapes 1).read.getD false)) (s.registers 2)

def rippleCarryBit (s : BitRAMState) : Bool :=
  xor (((s.tapes 0).read.getD false) && ((s.tapes 1).read.getD false))
    ((xor ((s.tapes 0).read.getD false) ((s.tapes 1).read.getD false)) && (s.registers 2))

theorem rippleRound_carry (s : BitRAMState) :
    (rippleRound s).registers 2 = rippleCarryBit s := by
  simp [rippleRound, fullAdderFinal, rippleLoaded, readTapeState,
    BitRAMState.setRegister, BitRAMState.setTape, rippleCarryBit]

theorem rippleRound_writes (s : BitRAMState) :
    TapeWrites (s.tapes 2) ((rippleRound s).tapes 2) [rippleSumBit s] := by
  constructor <;>
    simp [rippleRound, fullAdderFinal, rippleLoaded, readTapeState,
      BitRAMState.setRegister, BitRAMState.setTape, rippleSumBit, BitTape.write, writeCells]

theorem rippleStopped_tape (s : BitRAMState) (i : ℕ) :
    (rippleStopped s).tapes i = s.tapes i := by
  simp [rippleStopped, rippleLoaded, readTapeState]

theorem addBits_nonempty (carry : Bool) (xs ys : List Bool)
    (h : ¬(xs = [] ∧ ys = [])) :
    addBits carry xs ys =
      xor (xor (xs.headD false) (ys.headD false)) carry ::
        addBits (xor ((xs.headD false) && (ys.headD false))
          ((xor (xs.headD false) (ys.headD false)) && carry)) xs.tail ys.tail := by
  cases xs <;> cases ys <;> simp_all [addBits]

theorem rippleRound_inputs {s : BitRAMState} {xs ys : List Bool}
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    TapeRepresents ((rippleRound s).tapes 0) xs.tail ∧
      TapeRepresents ((rippleRound s).tapes 1) ys.tail := by
  rw [rippleRound_tape0, rippleRound_tape1]
  exact ⟨hx.moveRight, hy.moveRight⟩

theorem rippleRound_cost_nonempty {s : BitRAMState} {xs ys : List Bool}
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys)
    (h : ¬(xs = [] ∧ ys = [])) : rippleNonempty s = true ∧ rippleRoundCost s = 18 := by
  have ha := hx.read
  have hb := hy.read
  cases xs <;> cases ys <;> simp_all [rippleNonempty, rippleRoundCost]

/-- A call on two empty operand tapes terminates after the actual final
carry, if any. This is the base case of the uniform arithmetic loop. -/
theorem ripple_empty_run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) []) (hy : TapeRepresents (s.tapes 1) []) :
    ∃ cost final, cost ≤ 28 ∧ PricedSteps (rippleAdder.next input tape) cost s final ∧
      rippleAdder.next input tape final = none ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (addBits (s.registers 2) [] []) := by
  have ha : (s.tapes 0).read = none := by simpa using hx.read
  have hb : (s.tapes 1).read = none := by simpa using hy.read
  cases hc : s.registers 2 with
  | false =>
    refine ⟨9, rippleStopped s, by omega, ?_, rippleStopped_halt input tape s, ?_⟩
    · exact executeInstructions_sound _ (rippleStop_execute input tape s hpc ha hb hc)
    · rw [rippleStopped_tape]
      simpa [hc, addBits] using TapeWrites.refl (s.tapes 2)
  | true =>
    have hr := executeInstructions_sound _ (rippleRound_execute input tape s hpc (Or.inr hc))
    have hrCost : rippleRoundCost s = 19 := by simp [rippleRoundCost, rippleNonempty, ha, hb]
    rw [hrCost] at hr
    have hxy := rippleRound_inputs hx hy
    have hxa : ((rippleRound s).tapes 0).read = none := by simpa using hxy.1.read
    have hya : ((rippleRound s).tapes 1).read = none := by simpa using hxy.2.read
    have hc' : (rippleRound s).registers 2 = false := by
      rw [rippleRound_carry]
      simp [rippleCarryBit, ha, hb]
    have ht := executeInstructions_sound _ (rippleStop_execute input tape (rippleRound s)
      rfl hxa hya hc')
    refine ⟨28, rippleStopped (rippleRound s), by omega, ?_,
      rippleStopped_halt input tape (rippleRound s), ?_⟩
    · exact hr.trans ht
    · rw [rippleStopped_tape]
      simpa [rippleSumBit, ha, hb, hc, addBits] using rippleRound_writes s


end Maxwell.Cost
