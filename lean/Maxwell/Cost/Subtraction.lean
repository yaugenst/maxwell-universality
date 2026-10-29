import Maxwell.Cost.Arithmetic.Frame

/-! A uniform unsigned subtractor executed by the concrete priced BitRAM.
The result has exactly the larger input width; the final borrow records
underflow. No arithmetic operation or runtime is supplied as an oracle. -/

namespace Maxwell.Cost.Subtraction

def differenceBit (a b borrow : Bool) : Bool := xor (xor a b) borrow

def borrowBit (a b borrow : Bool) : Bool :=
  xor ((!a) && b) ((!(xor a b)) && borrow)

theorem full_bit_value (a b borrow : Bool) :
    (differenceBit a b borrow).toNat + b.toNat + borrow.toNat =
      a.toNat + 2 * (borrowBit a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- The two terms used for the borrow are disjoint, so a single XOR gate
implements their OR. -/
theorem borrowBit_standard (a b borrow : Bool) :
    borrowBit a b borrow = ((!a) && (b || borrow)) || (b && borrow) := by
  cases a <;> cases b <;> cases borrow <;> decide

def result (borrow : Bool) : List Bool → List Bool → List Bool × Bool
  | [], [] => ([], borrow)
  | a :: xs, [] =>
      let r := result (borrowBit a false borrow) xs []
      (differenceBit a false borrow :: r.1, r.2)
  | [], b :: ys =>
      let r := result (borrowBit false b borrow) [] ys
      (differenceBit false b borrow :: r.1, r.2)
  | a :: xs, b :: ys =>
      let r := result (borrowBit a b borrow) xs ys
      (differenceBit a b borrow :: r.1, r.2)
termination_by xs ys => xs.length + ys.length

theorem result_nonempty (borrow : Bool) (xs ys : List Bool)
    (h : ¬(xs = [] ∧ ys = [])) :
    result borrow xs ys =
      (differenceBit (xs.headD false) (ys.headD false) borrow ::
        (result (borrowBit (xs.headD false) (ys.headD false) borrow) xs.tail ys.tail).1,
       (result (borrowBit (xs.headD false) (ys.headD false) borrow) xs.tail ys.tail).2) := by
  cases xs <;> cases ys <;> simp_all [result]

theorem result_length (borrow : Bool) (xs ys : List Bool) :
    (result borrow xs ys).1.length = max xs.length ys.length := by
  induction xs generalizing ys borrow with
  | nil =>
    induction ys generalizing borrow with
    | nil => simp [result]
    | cons b ys ih => simp [result, ih]
  | cons a xs ih =>
    cases ys with
    | nil => simp [result, ih]
    | cons b ys => simp [result, ih, max_add_add_right]

/-- Exact unsigned subtraction relation, including the incoming and final
borrow. It remains meaningful when either input contains leading zeros. -/
theorem result_value (borrow : Bool) (xs ys : List Bool) :
    addressValue (result borrow xs ys).1 + addressValue ys + borrow.toNat =
      addressValue xs + 2 ^ max xs.length ys.length * (result borrow xs ys).2.toNat := by
  induction xs generalizing ys borrow with
  | nil =>
    induction ys generalizing borrow with
    | nil => simp [result, addressValue]
    | cons b ys ih =>
      have hrec := ih (borrowBit false b borrow)
      have hbit := full_bit_value false b borrow
      simp only [result, addressValue, List.length_nil, List.length_cons, Nat.zero_max,
        pow_succ, Bool.toNat_false] at hrec hbit ⊢
      nlinarith
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hrec := ih (borrowBit a false borrow) []
      have hbit := full_bit_value a false borrow
      simp only [result, addressValue, List.length_nil, List.length_cons, Nat.max_zero,
        pow_succ, Bool.toNat_false] at hrec hbit ⊢
      nlinarith
    | cons b ys =>
      have hrec := ih (borrowBit a b borrow) ys
      have hbit := full_bit_value a b borrow
      simp only [result, addressValue, List.length_cons, max_add_add_right, pow_succ] at hrec hbit ⊢
      nlinarith

theorem addressValue_lt_pow_length (bits : List Bool) : addressValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [addressValue]
  | cons b bits ih =>
    cases b <;> simp only [addressValue, List.length_cons, pow_succ, Bool.toNat_false,
      Bool.toNat_true] <;> omega

theorem final_borrow_iff (xs ys : List Bool) :
    (result false xs ys).2 = true ↔ addressValue xs < addressValue ys := by
  have hv := result_value false xs ys
  have hout := addressValue_lt_pow_length (result false xs ys).1
  rw [result_length] at hout
  cases hb : (result false xs ys).2 <;> simp only [hb, Bool.toNat_false, Bool.toNat_true,
    Bool.false_eq_true, false_iff, true_iff, mul_zero, mul_one, add_zero] at hv ⊢ <;> omega

/-- The wrapped output and final borrow reconstruct the exact signed
integer difference of the original unsigned operands. -/
theorem result_integer_difference (xs ys : List Bool) :
    (addressValue xs : ℤ) - (addressValue ys : ℤ) =
      (addressValue (result false xs ys).1 : ℤ) -
        (2 : ℤ) ^ max xs.length ys.length * ((result false xs ys).2.toNat : ℤ) := by
  have hv : addressValue (result false xs ys).1 + addressValue ys =
      addressValue xs + 2 ^ max xs.length ys.length * (result false xs ys).2.toNat := by
    simpa using result_value false xs ys
  have hi := congrArg (fun n : ℕ => (n : ℤ)) hv
  push_cast at hi
  linarith

/-- Initialization plus a fixed loop: tape 0 minus tape 1, output tape 2.
Register 2 carries the borrow; registers 0 through 11 are scratch. -/
def program : BitRAM := ⟨[
  .literal 2 false,
  .readTape 0 0 7,
  .readTape 1 1 8,
  .bitNot 9 7,
  .bitNot 10 8,
  .bitAnd 11 9 10,
  .branch 11 19 7,
  .bitXor 3 0 1,
  .bitXor 4 3 2,
  .bitNot 5 0,
  .bitAnd 5 5 1,
  .bitNot 6 3,
  .bitAnd 6 6 2,
  .bitXor 2 5 6,
  .writeTape 2 4,
  .tapeRight 0,
  .tapeRight 1,
  .tapeRight 2,
  .jump 1,
  .halt]⟩

def gates (s : BitRAMState) : BitRAMState :=
  let s := s.setRegister 3 (xor (s.registers 0) (s.registers 1))
  let s := s.setRegister 4 (xor (s.registers 3) (s.registers 2))
  let s := s.setRegister 5 (!s.registers 0)
  let s := s.setRegister 5 (s.registers 5 && s.registers 1)
  let s := s.setRegister 6 (!s.registers 3)
  let s := s.setRegister 6 (s.registers 6 && s.registers 2)
  s.setRegister 2 (xor (s.registers 5) (s.registers 6))

def round (s : BitRAMState) : BitRAMState :=
  let s := gates {(rippleLoaded s) with pc := 7}
  let s := s.setTape 2 ((s.tapes 2).write (some (s.registers 4)))
  let s := s.setTape 0 {s.tapes 0 with head := (s.tapes 0).head + 1}
  let s := s.setTape 1 {s.tapes 1 with head := (s.tapes 1).head + 1}
  let s := s.setTape 2 {s.tapes 2 with head := (s.tapes 2).head + 1}
  {s with pc := 1}

def stopped (s : BitRAMState) : BitRAMState := {(rippleLoaded s) with pc := 19}

def roundDifference (s : BitRAMState) : Bool :=
  differenceBit ((s.tapes 0).read.getD false) ((s.tapes 1).read.getD false) (s.registers 2)

def roundBorrow (s : BitRAMState) : Bool :=
  borrowBit ((s.tapes 0).read.getD false) ((s.tapes 1).read.getD false) (s.registers 2)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem round_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (active : rippleNonempty s = true) :
    executeInstructions (program.next input tape) 18 s = some (round s, 20) := by
  cases ha : (s.tapes 0).read <;> cases hb : (s.tapes 1).read <;>
    simp [rippleNonempty, ha, hb] at active
  all_goals simp (config := { maxSteps := 500000 }) [executeInstructions, program, BitRAM.next,
    round, gates, rippleLoaded, readTapeState, BitTape.write, hpc, ha, hb]

theorem stop_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1)
    (ha : (s.tapes 0).read = none) (hb : (s.tapes 1).read = none) :
    executeInstructions (program.next input tape) 6 s = some (stopped s, 8) := by
  simp [executeInstructions, program, BitRAM.next, stopped, rippleLoaded,
    readTapeState, hpc, ha, hb]

theorem stopped_halt (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) :
    program.next input tape (stopped s) = none := by simp [program, BitRAM.next, stopped]

theorem round_tape0 (s : BitRAMState) :
    (round s).tapes 0 = {s.tapes 0 with head := (s.tapes 0).head + 1} := by
  simp [round, gates, rippleLoaded, readTapeState, BitRAMState.setRegister, BitRAMState.setTape]

theorem round_tape1 (s : BitRAMState) :
    (round s).tapes 1 = {s.tapes 1 with head := (s.tapes 1).head + 1} := by
  simp [round, gates, rippleLoaded, readTapeState, BitRAMState.setRegister, BitRAMState.setTape]

theorem round_borrow (s : BitRAMState) : (round s).registers 2 = roundBorrow s := by
  simp [round, gates, rippleLoaded, readTapeState, roundBorrow, borrowBit,
    BitRAMState.setRegister, BitRAMState.setTape]

theorem round_writes (s : BitRAMState) :
    TapeWrites (s.tapes 2) ((round s).tapes 2) [roundDifference s] := by
  constructor <;>
    simp [round, gates, rippleLoaded, readTapeState, roundDifference, differenceBit,
      BitRAMState.setRegister, BitRAMState.setTape, BitTape.write, writeCells]

theorem stopped_tape (s : BitRAMState) (i : ℕ) : (stopped s).tapes i = s.tapes i := by
  simp [stopped, rippleLoaded, readTapeState]

theorem stopped_borrow (s : BitRAMState) : (stopped s).registers 2 = s.registers 2 := by
  simp [stopped, rippleLoaded, readTapeState]

theorem round_inputs {s : BitRAMState} {xs ys : List Bool}
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    TapeRepresents ((round s).tapes 0) xs.tail ∧ TapeRepresents ((round s).tapes 1) ys.tail := by
  rw [round_tape0, round_tape1]
  exact ⟨hx.moveRight, hy.moveRight⟩

/-- Every iteration executes the same finite code and writes one bit.
The ending borrow is retained even when both input tapes become blank. -/
theorem loop_simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (hpc : s.pc = 1)
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    ∃ final, PricedSteps (program.next input tape) (20 * max xs.length ys.length + 8) s final ∧
      final.pc = 19 ∧ final.registers 2 = (result (s.registers 2) xs ys).2 ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (result (s.registers 2) xs ys).1 ∧
      final.tapes 0 = {s.tapes 0 with head := (s.tapes 0).head + max xs.length ys.length} ∧
      final.tapes 1 = {s.tapes 1 with head := (s.tapes 1).head + max xs.length ys.length} := by
  by_cases hempty : xs = [] ∧ ys = []
  · rcases hempty with ⟨rfl, rfl⟩
    have ha : (s.tapes 0).read = none := by simpa using hx.read
    have hb : (s.tapes 1).read = none := by simpa using hy.read
    refine ⟨stopped s, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using executeInstructions_sound _ (stop_execute input tape s hpc ha hb)
    · simpa [result] using stopped_borrow s
    · rw [stopped_tape]
      simpa [result] using TapeWrites.refl (s.tapes 2)
    · simp [stopped_tape]
    · simp [stopped_tape]
  · have hactive : rippleNonempty s = true := (rippleRound_cost_nonempty hx hy hempty).1
    have hstep := executeInstructions_sound _ (round_execute input tape s hpc hactive)
    have hinputs := round_inputs hx hy
    obtain ⟨final, hrest, hfinalpc, hborrow, hwrites, ht0, ht1⟩ :=
      loop_simulation input tape (round s) xs.tail ys.tail rfl hinputs.1 hinputs.2
    have hlength : max xs.length ys.length = max xs.tail.length ys.tail.length + 1 := by
      cases xs <;> cases ys <;> simp_all
    have hresult := result_nonempty (s.registers 2) xs ys hempty
    have hread0 : (s.tapes 0).read.getD false = xs.headD false := by
      rw [hx.read]
      cases xs <;> rfl
    have hread1 : (s.tapes 1).read.getD false = ys.headD false := by
      rw [hy.read]
      cases ys <;> rfl
    refine ⟨final, ?_, hfinalpc, ?_, ?_, ?_, ?_⟩
    · convert hstep.trans hrest using 1
      rw [hlength]
      omega
    · rw [hresult]
      simpa only [round_borrow, roundBorrow, hread0, hread1] using hborrow
    · have hw := (round_writes s).trans hwrites
      rw [hresult]
      simpa only [round_borrow, roundBorrow, roundDifference, hread0, hread1,
        List.singleton_append] using hw
    · rw [ht0, round_tape0, hlength]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      omega
    · rw [ht1, round_tape1, hlength]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      omega
termination_by xs.length + ys.length
decreasing_by exact tails_length_lt _ _ hempty

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The same scratch frame as the ripple adder is preserved, enabling
ordinary code linking and tape renaming. -/
theorem next_frame (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ)
    (h : program.next input tape s = some ⟨t, extra⟩) : rippleFrame t = rippleFrame s := by
  have hpc := program.next_code_present input tape s ⟨t, extra⟩ h
  change s.pc < 20 at hpc
  interval_cases hp : s.pc <;>
    simp only [BitRAM.next, program, hp, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at h
  all_goals try contradiction
  all_goals
    simp only [Option.some.injEq, PricedStep.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [rippleFrame, setRegister_address, setRegister_inputHead,
      setRegister_memory, setRegister_randomCursor, setRegister_output,
      setRegister_registers, setRegister_tapes, setTape_address, setTape_inputHead,
      setTape_memory, setTape_randomCursor, setTape_output, setTape_registers, setTape_tapes]
  all_goals congr 1

theorem execution_frame (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ} (h : PricedSteps (program.next input tape) cost s t) :
    rippleFrame t = rippleFrame s := h.conserved rippleFrame (next_frame input tape)

/-- Complete subtraction initializes its own borrow bit. The exact cost
comes from the startup, per-bit interpreter trace, and final blank check. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    ∃ final, PricedSteps (program.next input tape) (20 * max xs.length ys.length + 9) s final ∧
      final.pc = 19 ∧ final.registers 2 = (result false xs ys).2 ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (result false xs ys).1 ∧
      final.tapes 0 = {s.tapes 0 with head := (s.tapes 0).head + max xs.length ys.length} ∧
      final.tapes 1 = {s.tapes 1 with head := (s.tapes 1).head + max xs.length ys.length} ∧
      rippleFrame final = rippleFrame s := by
  have hstart : PricedSteps (program.next input tape) 1 s (s.setRegister 2 false) := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, hpc]
  obtain ⟨final, hsteps, hp, hb, hw, ht0, ht1⟩ := loop_simulation input tape (s.setRegister 2 false)
    xs ys (by simp [hpc]) hx hy
  have hall : PricedSteps (program.next input tape) (20 * max xs.length ys.length + 9) s final := by
    convert hstart.trans hsteps using 1
    omega
  refine ⟨final, hall, hp, ?_, hw, ht0, ht1, execution_frame input tape hall⟩
  simpa using hb

/-- The capped actual interpreter returns subtraction modulo the chosen
bit width, with final borrow exactly characterizing unsigned comparison. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs ys : List Bool) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) xs) (hy : TapeRepresents (s.tapes 1) ys) :
    ∃ final, (runPriced (program.next input tape)
        (20 * max xs.length ys.length + 10) s).finished = some final ∧
      (runPriced (program.next input tape)
        (20 * max xs.length ys.length + 10) s).instructions = 20 * max xs.length ys.length + 9 ∧
      TapeWrites (s.tapes 2) (final.tapes 2) (result false xs ys).1 ∧
      (result false xs ys).1.length = max xs.length ys.length ∧
      addressValue (result false xs ys).1 + addressValue ys =
        addressValue xs + 2 ^ max xs.length ys.length * (final.registers 2).toNat ∧
      (final.registers 2 = true ↔ addressValue xs < addressValue ys) ∧
      rippleFrame final = rippleFrame s := by
  obtain ⟨final, hs, hp, hb, hw, _, _, hf⟩ := simulation input tape s xs ys hpc hx hy
  have hhalt : program.next input tape final = none := by simp [BitRAM.next, program, hp]
  have hr := hs.runPriced hhalt
  refine ⟨final, ?_, ?_, hw, result_length false xs ys, ?_, ?_, hf⟩
  · simpa [Nat.add_assoc] using hr.1
  · simpa [Nat.add_assoc] using hr.2
  · rw [hb]
    simpa using result_value false xs ys
  · rw [hb]
    exact final_borrow_iff xs ys

end Maxwell.Cost.Subtraction
