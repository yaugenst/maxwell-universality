import Maxwell.Cost.SelectedParameters.RationalChoice
import Maxwell.Cost.SelectedParameters.RationalPower

namespace Maxwell.Cost.SelectedParameters.RationalScript
open Structured
open Rational

inductive Operation where
  | literal (numerator denominator : ℕ)
  | basic (op : Basic) (a b c d : ℕ)
  | choice (op : Choice) (a b c d : ℕ)
  | power (exponent a b : ℕ)
  deriving DecidableEq, Repr

structure Instruction where
  operation : Operation
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq, Repr

def Instruction.Valid (extra : Finset ℕ) (a : Instruction) : Prop :=
  a.numerator∈extra ∧ a.denominator∈extra ∧ a.numerator≠a.denominator ∧
  match a.operation with
  | .literal _ _ => True
  | .basic _ x y z w | .choice _ x y z w => x∈extra ∧ y∈extra ∧ z∈extra ∧ w∈extra
  | .power _ x y => x∈extra ∧ y∈extra ∧
      x≠a.numerator ∧ x≠a.denominator ∧ y≠a.numerator ∧ y≠a.denominator

def Instruction.Enabled (a : Instruction) (v : ℕ→ℕ) : Prop :=
  match a.operation with
  | .choice _ _ b _ d => 0<v b ∧ 0<v d
  | _ => True

def Instruction.result (a : Instruction) (v : ℕ→ℕ) : ℕ×ℕ :=
  match a.operation with
  | .literal n d => (n,d)
  | .basic op x y z w => pair op (v x) (v y) (v z) (v w)
  | .choice op x y z w => choicePair op (v x) (v y) (v z) (v w)
  | .power k x y => powerPair k (v x) (v y)

def Instruction.update (a : Instruction) (v : ℕ→ℕ) : ℕ→ℕ :=
  after v a.numerator a.denominator (a.result v)

def literalInstructions (num den n d : ℕ) : List NatAssign.Instruction :=
  [.literal num n,.literal den d]++clear

def Instruction.code (a : Instruction) : Code :=
  match a.operation with
  | .literal n d => NatAssign.code (literalInstructions a.numerator a.denominator n d)
  | .basic op x y z w => basicCode op x y z w a.numerator a.denominator
  | .choice op x y z w => choiceCode op x y z w a.numerator a.denominator
  | .power k x y => powerCode k x y a.numerator a.denominator

def Clean (v : ℕ→ℕ) : Prop := ∀ i∈common, v i=0

def Instruction.nextWidth (a : Instruction) (B : ℕ) : ℕ :=
  match a.operation with
  | .literal n d => B+n.bits.length+d.bits.length
  | .basic .. => 2*B+1
  | .choice .. => B
  | .power k _ _ => (k+1)*B+1

def Instruction.growth (a : Instruction) : ℕ :=
  match a.operation with
  | .literal n d => n.bits.length+d.bits.length+1
  | .basic .. => 2
  | .choice .. => 1
  | .power k _ _ => k+2

def Instruction.coefficient (a : Instruction) : ℕ :=
  match a.operation with
  | .literal n d => 3000*8^9*(n.bits.length+d.bits.length+1)^2
  | .basic .. => 3000*8^19
  | .choice .. => 3000*8^4+8000+1+3000*8^9
  | .power k _ _ => 12000*8^(2*k+9)

def sequence : List Instruction → Code
  | [] => .skip
  | a::rest => .seq a.code (sequence rest)

def fold : List Instruction → (ℕ→ℕ) → (ℕ→ℕ)
  | [],v => v
  | a::rest,v => fold rest (a.update v)

def Enabled : List Instruction → (ℕ→ℕ) → Prop
  | [],_ => True
  | a::rest,v => a.Enabled v ∧ Enabled rest (a.update v)

def widthFactor : List Instruction → ℕ
  | [] => 1
  | a::rest => widthFactor rest*a.growth

def costFactor : List Instruction → ℕ
  | [] => 1
  | a::rest => a.coefficient+costFactor rest*a.growth^2

def outputs (instructions : List Instruction) : Finset ℕ :=
  (instructions.flatMap fun a => [a.numerator,a.denominator]).toFinset

def workspace (instructions : List Instruction) : Finset ℕ := {0,1,2,3}∪common∪outputs instructions

/-- The prologue is an actual seven-word clear. The empty script also
establishes the shared arithmetic workspace invariant. -/
def code (instructions : List Instruction) : Code := .seq (NatAssign.code clear) (sequence instructions)
def values (instructions : List Instruction) (v : ℕ→ℕ) : ℕ→ℕ := fold instructions (clean v)
def coefficient (instructions : List Instruction) : ℕ := 3000*8^7+costFactor instructions
def program (instructions : List Instruction) : BitRAM := (code instructions).compile

end Maxwell.Cost.SelectedParameters.RationalScript
