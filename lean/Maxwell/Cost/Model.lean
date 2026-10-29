import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Primitive-operation semantics

Programs in this module are a free language of explicit RAM, random-bit,
and Boolean-bit instructions. `steps` counts executed instructions along
an execution, not a runtime field asserted by an implementation. Ordinary
Lean recursion builds the program; arithmetic on the simulated values is
performed by instructions. Random bits are supplied by an explicit tape.
-/

namespace Maxwell.Cost

inductive ValueType where
  | bit | real | index | unit

abbrev ValueType.denote : ValueType → Type
  | .bit => Bool
  | .real => ℝ
  | .index => ℕ
  | .unit => Unit

inductive Instruction : ValueType → Type where
  | bitNot : Bool → Instruction .bit
  | bitAnd : Bool → Bool → Instruction .bit
  | bitXor : Bool → Bool → Instruction .bit
  | readBit : Bool → Instruction .bit
  | writeBit : Bool → Instruction .unit
  | add : ℝ → ℝ → Instruction .real
  | multiply : ℝ → ℝ → Instruction .real
  | compare : ℝ → ℝ → Instruction .bit
  | read : ℝ → Instruction .real
  | write : ℝ → Instruction .unit
  | draw : Bool → Instruction .bit
  | readIndex : ℕ → Instruction .index
  | addIndex : ℕ → ℕ → Instruction .index
  | writeIndex : ℕ → Instruction .unit

noncomputable def Instruction.execute {α : ValueType} : Instruction α → α.denote
  | .bitNot b => !b
  | .bitAnd a b => a && b
  | .bitXor a b => xor a b
  | .readBit b => b
  | .writeBit _ => ()
  | .add a b => a + b
  | .multiply a b => a * b
  | .compare a b => decide (a ≤ b)
  | .read a => a
  | .write _ => ()
  | .draw b => b
  | .readIndex n => n
  | .addIndex a b => a + b
  | .writeIndex _ => ()

inductive Program (α : Type) : Type where
  | halt : α → Program α
  | step {β : ValueType} : Instruction β → (β.denote → Program α) → Program α

noncomputable def Program.result {α : Type} : Program α → α
  | .halt a => a
  | .step i next => (next i.execute).result

noncomputable def Program.steps {α : Type} : Program α → ℕ
  | .halt _ => 0
  | .step i next => (next i.execute).steps + 1

def Program.bind {α β : Type} : Program α → (α → Program β) → Program β
  | .halt a, k => k a
  | .step i next, k => .step i (fun v => (next v).bind k)

def perform {α : ValueType} (i : Instruction α) : Program α.denote :=
  .step i .halt

instance : Monad Program where
  pure := .halt
  bind := Program.bind

@[simp] theorem result_halt {α : Type} (a : α) :
    (Program.halt a).result = a := rfl

@[simp] theorem steps_halt {α : Type} (a : α) :
    (Program.halt a).steps = 0 := rfl

@[simp] theorem result_perform {α : ValueType} (i : Instruction α) :
    (perform i).result = i.execute := rfl

@[simp] theorem steps_perform {α : ValueType} (i : Instruction α) :
    (perform i).steps = 1 := rfl

@[simp] theorem result_bind {α β : Type} (p : Program α) (k : α → Program β) :
    (p.bind k).result = (k p.result).result := by
  induction p with
  | halt a => rfl
  | @step γ i next ih =>
    simp only [Program.bind, Program.result, ih]

@[simp] theorem steps_bind {α β : Type} (p : Program α) (k : α → Program β) :
    (p.bind k).steps = p.steps + (k p.result).steps := by
  induction p with
  | halt a => simp [Program.bind, Program.steps, Program.result]
  | @step γ i next ih =>
    simp only [Program.bind, Program.steps, Program.result, ih]
    omega

/-- Every random bit is an instruction, so random input is never free. -/
def drawBits : List Bool → Program (List Bool)
  | [] => pure []
  | b :: bs => do
      let v ← perform (.draw b)
      let vs ← drawBits bs
      pure (v :: vs)

@[simp] theorem drawBits_result (bits : List Bool) :
    (drawBits bits).result = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    change ((drawBits bs).bind (fun vs => .halt (b :: vs))).result = b :: bs
    simp [ih]

@[simp] theorem drawBits_steps (bits : List Bool) :
    (drawBits bits).steps = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp [drawBits, bind, Pure.pure, Instruction.execute, ih, Nat.add_comm, Program.bind, Program.steps, perform]

/-- Writing a whole vector explicitly charges all ambient coordinates. -/
def writeWords : List ℝ → Program Unit
  | [] => pure ()
  | a :: as => do
      perform (.write a)
      writeWords as

@[simp] theorem writeWords_steps (values : List ℝ) :
    (writeWords values).steps = values.length := by
  induction values with
  | nil => rfl
  | cons a as ih =>
    simp [writeWords, bind, Instruction.execute, ih, Nat.add_comm, Program.bind, Program.steps, perform]

/-- Bit output is separate from unit-cost real-word output. -/
def writeBits : List Bool → Program Unit
  | [] => pure ()
  | b :: bs => do
      perform (.writeBit b)
      writeBits bs

@[simp] theorem writeBits_steps (bits : List Bool) :
    (writeBits bits).steps = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp [writeBits, bind, Instruction.execute, ih, Nat.add_comm, Program.bind, Program.steps, perform]

end Maxwell.Cost
