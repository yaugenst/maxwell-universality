import Maxwell.Cost.FixedWidth
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.PositiveGraph.DiagonalWord
open Structured
set_option maxHeartbeats 1800000

/-- The signed numerator change of one positive-graph incidence. -/
def delta (negative half mediator : Bool) : ℤ :=
  (if negative then 1 else -1) *
    (if mediator then (if half then 4 else 2) else (if half then 1 else 2))

def updated (value : ℕ) (negative half mediator : Bool) : ℕ :=
  (((value : ℤ) + delta negative half mediator) % 16).toNat

theorem updated_lt (value : ℕ) (negative half mediator : Bool) :
    updated value negative half mediator < 16 := by
  have hn := Int.emod_nonneg ((value : ℤ) + delta negative half mediator) (by norm_num : (16 : ℤ) ≠ 0)
  have hl := Int.emod_lt_of_pos ((value : ℤ) + delta negative half mediator) (by norm_num : (0 : ℤ) < 16)
  unfold updated
  omega

/-- Read four bits, select the first affected position, propagate carry or
borrow, then write the four bits back in reverse order. -/
def program : BitRAM := ⟨[
  .readTape 120 50 55, .tapeRight 120,
  .readTape 120 51 55, .tapeRight 120,
  .readTape 120 52 55, .tapeRight 120,
  .readTape 120 53 55,
  .literal 54 true,
  .branch 45 9 14,
  .branch 47 18 10,
  .bitXor 55 50 44, .bitNot 55 55, .bitXor 50 50 54, .bitAnd 54 54 55,
  .bitXor 55 51 44, .bitNot 55 55, .bitXor 51 51 54, .bitAnd 54 54 55,
  .bitXor 55 52 44, .bitNot 55 55, .bitXor 52 52 54, .bitAnd 54 54 55,
  .bitXor 55 53 44, .bitNot 55 55, .bitXor 53 53 54, .bitAnd 54 54 55,
  .writeTape 120 53, .tapeLeft 120,
  .writeTape 120 52, .tapeLeft 120,
  .writeTape 120 51, .tapeLeft 120,
  .writeTape 120 50, .halt]⟩

def cost (half mediator : Bool) : ℕ := if half then (if mediator then 30 else 38) else 33

def load (b : Fin 4 → Bool) (r : ℕ → Bool) : ℕ → Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update r 50 (b 0)) 51 (b 1)) 52 (b 2)) 53 (b 3)) 55 true) 54 true

def round (j : ℕ) (negative : Bool) (r : ℕ → Bool) : ℕ → Bool :=
  let c := !(xor (r (50+j)) negative)
  Function.update (Function.update (Function.update r 55 c)
    (50+j) (xor (r (50+j)) (r 54))) 54 (r 54 && c)

def registers (b : Fin 4 → Bool) (negative half mediator : Bool) (r : ℕ → Bool) : ℕ → Bool :=
  let r0 := load b r
  let r1 := if half then (if mediator then r0 else round 1 negative (round 0 negative r0))
    else round 1 negative r0
  round 3 negative (round 2 negative r1)

def word (b : Fin 4 → Bool) (negative half mediator : Bool) : List Bool :=
  let r := registers b negative half mediator (fun _ => false)
  [r 50, r 51, r 52, r 53]

/-- A finite, kernel-checked truth table connects the Boolean circuit to
signed arithmetic modulo sixteen. -/
theorem word_correct : ∀ (b : Fin 4 → Bool) (negative half mediator : Bool),
    word b negative half mediator = FixedWidth.bits 4
      (updated (addressValue (List.ofFn b)) negative half mediator).bits := by
  decide

private theorem registers_read (b : Fin 4 → Bool) (negative half mediator : Bool)
    (r : ℕ → Bool) (j : Fin 4) :
    registers b negative half mediator r (50+j.val) =
      registers b negative half mediator (fun _ => false) (50+j.val) := by
  fin_cases j <;> cases half <;> cases mediator <;>
    simp [registers, round, load]

private theorem registers_frame (b : Fin 4 → Bool) (negative half mediator : Bool)
    (r : ℕ → Bool) (i : ℕ) (hi : i < 50 ∨ 55 < i) :
    registers b negative half mediator r i = r i := by
  cases half <;> cases mediator <;>
    simp [registers, round, load, Function.update_of_ne (show i ≠ 50 by omega),
      Function.update_of_ne (show i ≠ 51 by omega), Function.update_of_ne (show i ≠ 52 by omega),
      Function.update_of_ne (show i ≠ 53 by omega), Function.update_of_ne (show i ≠ 54 by omega),
      Function.update_of_ne (show i ≠ 55 by omega)]

def rewritten (old : BitTape) (origin : ℤ) (r : ℕ → Bool) : BitTape :=
  ⟨origin, Function.update (Function.update (Function.update (Function.update
    old.cells (origin+3) (some (r 53))) (origin+2) (some (r 52)))
      (origin+1) (some (r 51))) origin (some (r 50))⟩

def finish (s : BitRAMState) (b : Fin 4 → Bool) (origin : ℤ)
    (negative half mediator : Bool) : BitRAMState :=
  let r := registers b negative half mediator s.registers
  {s with
    pc := 33
    registers := r
    tapes := Function.update s.tapes 120 (rewritten (s.tapes 120) origin r)}

def firstPC (half mediator : Bool) : ℕ := if half then (if mediator then 18 else 10) else 14

def loadedState (s : BitRAMState) (b : Fin 4 → Bool) (origin : ℤ) (half mediator : Bool) : BitRAMState :=
  {s with
    pc := firstPC half mediator
    registers := load b s.registers
    tapes := Function.update s.tapes 120 {s.tapes 120 with head := origin+3}}

private theorem prefix_steps (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (b : Fin 4 → Bool) (origin : ℤ) (half mediator : Bool)
    (hw : s.val.tapes 120 = BitTape.shifted (List.ofFn b) origin)
    (hh : s.val.registers 45 = half) (hm : s.val.registers 47 = mediator) :
    PricedSteps (program.next input randomTape) (if half then 14 else 13)
      s.val (loadedState s.val b origin half mediator) := by
  apply executeInstructions_sound (instructions := if half then 10 else 9)
  cases half <;> cases mediator <;>
    simp [executeInstructions, program, BitRAM.next, s.property, hw, hh, hm,
      loadedState, firstPC, load, BitTape.shifted, BitTape.read,
      BitRAMState.setRegister, BitRAMState.setTape, List.ofFn_succ, add_assoc]
  all_goals funext i
  all_goals by_cases h : i = 55 <;> simp [Function.update_apply, h]

def roundState (j : Fin 4) (negative : Bool) (s : BitRAMState) : BitRAMState :=
  {s with pc := 10+4*(j.val+1), registers := round j.val negative s.registers}

private theorem round_steps (j : Fin 4) (negative : Bool)
    (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState)
    (hp : s.pc = 10+4*j.val) (hn : s.registers 44 = negative) :
    PricedSteps (program.next input randomTape) 4 s (roundState j negative s) := by
  apply executeInstructions_sound (instructions := 4)
  fin_cases j <;>
    simp [executeInstructions, program, BitRAM.next, hp, hn, roundState, round,
      BitRAMState.setRegister]

private theorem round_flag (j : Fin 4) (negative : Bool) (s : BitRAMState) :
    (roundState j negative s).registers 44 = s.registers 44 := by
  fin_cases j <;> simp [roundState, round]

def writeFinish (s : BitRAMState) (origin : ℤ) : BitRAMState :=
  {s with pc := 33, tapes := Function.update s.tapes 120 (rewritten (s.tapes 120) origin s.registers)}

private theorem write_steps (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (origin : ℤ) (hp : s.pc = 26) (hh : (s.tapes 120).head = origin+3) :
    PricedSteps (program.next input randomTape) 7 s (writeFinish s origin) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions, program, BitRAM.next, hp, hh, writeFinish, rewritten,
    BitRAMState.setTape, BitTape.write, add_sub_assoc]

private theorem run_steps (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (b : Fin 4 → Bool) (origin : ℤ) (negative half mediator : Bool)
    (hw : s.val.tapes 120 = BitTape.shifted (List.ofFn b) origin)
    (hn : s.val.registers 44 = negative) (hh : s.val.registers 45 = half)
    (hm : s.val.registers 47 = mediator) :
    PricedSteps (program.next input randomTape) (cost half mediator - 1)
      s.val (finish s.val b origin negative half mediator) := by
  have ep := prefix_steps input randomTape s b origin half mediator hw hh hm
  have hf : (loadedState s.val b origin half mediator).registers 44 = negative := by
    simpa [loadedState, load] using hn
  cases half <;> cases mediator
  · have e1 := round_steps 1 negative input randomTape _ rfl hf
    have e2 := round_steps 2 negative input randomTape _ rfl ((round_flag 1 negative _).trans hf)
    have e3 := round_steps 3 negative input randomTape _ rfl
      ((round_flag 2 negative _).trans ((round_flag 1 negative _).trans hf))
    have ew := write_steps input randomTape (roundState 3 negative (roundState 2 negative (roundState 1 negative (loadedState s.val b origin false false)))) origin rfl (by simp [roundState, loadedState])
    convert ep.trans (e1.trans (e2.trans (e3.trans ew))) using 1 <;> first | rfl | simp [finish, writeFinish, roundState, loadedState, registers, rewritten]
  · have e1 := round_steps 1 negative input randomTape _ rfl hf
    have e2 := round_steps 2 negative input randomTape _ rfl ((round_flag 1 negative _).trans hf)
    have e3 := round_steps 3 negative input randomTape _ rfl
      ((round_flag 2 negative _).trans ((round_flag 1 negative _).trans hf))
    have ew := write_steps input randomTape (roundState 3 negative (roundState 2 negative (roundState 1 negative (loadedState s.val b origin false true)))) origin rfl (by simp [roundState, loadedState])
    convert ep.trans (e1.trans (e2.trans (e3.trans ew))) using 1 <;> first | rfl | simp [finish, writeFinish, roundState, loadedState, registers, rewritten]
  · have e0 := round_steps 0 negative input randomTape _ rfl hf
    have e1 := round_steps 1 negative input randomTape _ rfl ((round_flag 0 negative _).trans hf)
    have e2 := round_steps 2 negative input randomTape _ rfl
      ((round_flag 1 negative _).trans ((round_flag 0 negative _).trans hf))
    have e3 := round_steps 3 negative input randomTape _ rfl
      ((round_flag 2 negative _).trans ((round_flag 1 negative _).trans ((round_flag 0 negative _).trans hf)))
    have ew := write_steps input randomTape (roundState 3 negative (roundState 2 negative (roundState 1 negative (roundState 0 negative (loadedState s.val b origin true false))))) origin rfl (by simp [roundState, loadedState])
    convert ep.trans (e0.trans (e1.trans (e2.trans (e3.trans ew)))) using 1 <;> first | rfl | simp [finish, writeFinish, roundState, loadedState, registers, rewritten]
  · have e2 := round_steps 2 negative input randomTape _ rfl hf
    have e3 := round_steps 3 negative input randomTape _ rfl ((round_flag 2 negative _).trans hf)
    have ew := write_steps input randomTape (roundState 3 negative (roundState 2 negative (loadedState s.val b origin true true))) origin rfl (by simp [roundState, loadedState])
    convert ep.trans (e2.trans (e3.trans ew)) using 1 <;>
      first | rfl | simp [finish, writeFinish, roundState, loadedState, registers, rewritten]

private theorem rewritten_eq (a : Fin 4 → Bool) (origin : ℤ) (r : ℕ → Bool) :
    rewritten (BitTape.shifted (List.ofFn a) origin) origin r =
      BitTape.shifted [r 50, r 51, r 52, r 53] origin := by
  apply BitTape.ext
  · rfl
  · funext p
    by_cases h0 : p = origin
    · subst p; simp [rewritten, BitTape.shifted]
    by_cases h1 : p = origin+1
    · subst p; simp [rewritten, BitTape.shifted]
    by_cases h2 : p = origin+2
    · subst p; simp [rewritten, BitTape.shifted]
    by_cases h3 : p = origin+3
    · subst p; simp [rewritten, BitTape.shifted]
    by_cases hp : origin ≤ p
    · have hn : 4 ≤ (p-origin).toNat := by omega
      have hz : 4 ≤ p-origin := by omega
      simp [rewritten, BitTape.shifted, h0, h1, h2, h3, hp, hz]
    · simp [rewritten, BitTape.shifted, h0, h1, h2, h3, hp]

private def inputBits (n : Fin 16) : Fin 4 → Bool := fun j => n.val.testBit j.val

private theorem inputBits_correct : ∀ n : Fin 16,
    List.ofFn (inputBits n) = FixedWidth.bits 4 n.val.bits ∧
      addressValue (List.ofFn (inputBits n)) = n.val := by decide

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  inputHead : t.inputHead = s.inputHead
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 120 → t.tapes i = s.tapes i
  registers : ∀ i, i < 50 ∨ 55 < i → t.registers i = s.registers i

private theorem finish_frame (s : BitRAMState) (b : Fin 4 → Bool) (origin : ℤ)
    (negative half mediator : Bool) : Frame s (finish s b origin negative half mediator) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i hi; simp [finish, hi]
  · exact registers_frame b negative half mediator s.registers

theorem cost_le (half mediator : Bool) : cost half mediator ≤ 38 := by
  cases half <;> cases mediator <;> decide

/-- Actual fixed code updates the four cells in place and restores their head.
All flags, all other tapes, and all registers outside 50–55 are preserved. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (value : ℕ) (hvalue : value < 16) (origin : ℤ)
    (negative half mediator : Bool)
    (hw : s.val.tapes 120 = BitTape.shifted (FixedWidth.bits 4 value.bits) origin)
    (hn : s.val.registers 44 = negative) (hh : s.val.registers 45 = half)
    (hm : s.val.registers 47 = mediator) :
    ∃ t : Store, Executes input randomTape (.call program) (cost half mediator) s t ∧
      t.val.tapes 120 = BitTape.shifted
        (FixedWidth.bits 4 (updated value negative half mediator).bits) origin ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧
      t.val.registers 47 = mediator ∧ Frame s.val t.val := by
  let b := inputBits ⟨value, hvalue⟩
  have hb := inputBits_correct ⟨value, hvalue⟩
  have hword : s.val.tapes 120 = BitTape.shifted (List.ofFn b) origin := by rw [hb.1]; exact hw
  let t := Store.ofState (finish s.val b origin negative half mediator)
  have he := run_steps input randomTape s b origin negative half mediator hword hn hh hm
  have hf : Frame s.val t.val := by
    have h := finish_frame s.val b origin negative half mediator
    exact ⟨h.address, h.inputHead, h.memory, h.randomCursor, h.output, h.tapes, h.registers⟩
  refine ⟨t, ?_, ?_, (hf.registers 44 (by omega)).trans hn,
    (hf.registers 45 (by omega)).trans hh, (hf.registers 47 (by omega)).trans hm, hf⟩
  · have hc : cost half mediator - 1 + 1 = cost half mediator := by
      cases half <;> cases mediator <;> decide
    rw [← hc]
    exact Executes.call program s _ _ he rfl
  · change (finish s.val b origin negative half mediator).tapes 120 = _
    simp only [finish, Function.update_self]
    rw [hword, rewritten_eq]
    have hr (j : Fin 4) := registers_read b negative half mediator s.val.registers j
    have h0 := hr 0
    have h1 := hr 1
    have h2 := hr 2
    have h3 := hr 3
    change registers b negative half mediator s.val.registers 50 = _ at h0
    change registers b negative half mediator s.val.registers 51 = _ at h1
    change registers b negative half mediator s.val.registers 52 = _ at h2
    change registers b negative half mediator s.val.registers 53 = _ at h3
    rw [h0, h1, h2, h3]
    change BitTape.shifted (word b negative half mediator) origin = _
    rw [word_correct, hb.2]

theorem compiled_run (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (value : ℕ) (hvalue : value < 16) (origin : ℤ)
    (negative half mediator : Bool)
    (hw : s.val.tapes 120 = BitTape.shifted (FixedWidth.bits 4 value.bits) origin)
    (hn : s.val.registers 44 = negative) (hh : s.val.registers 45 = half)
    (hm : s.val.registers 47 = mediator) :
    ∃ t : Store,
      (runPriced ((Code.call program).compile.next input randomTape) 39 s.val).finished =
        some (t.place (Code.call program).size) ∧
      (runPriced ((Code.call program).compile.next input randomTape) 39 s.val).instructions ≤ 38 ∧
      t.val.tapes 120 = BitTape.shifted
        (FixedWidth.bits 4 (updated value negative half mediator).bits) origin ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧
      t.val.registers 47 = mediator ∧ Frame s.val t.val := by
  obtain ⟨t, he, ht⟩ := executes input randomTape s value hvalue origin negative half mediator hw hn hh hm
  have hc := cost_le half mediator
  have hr := he.compiled_run 39 (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ht⟩

end Maxwell.Cost.PositiveGraph.DiagonalWord
