import Maxwell.Cost.SparseEmission.ReadGate

/-! The five literal archive tags bind the operational reader to the
rational circuit's actual gate records and chronological stream. -/
namespace Maxwell.Cost.SparseEmission.ReadGate
open Maxwell.Logical

inductive Kind where
  | zero
  | half (parent : ℕ)
  | negative (parent : ℕ)
  | copy (parent : ℕ)
  | add (left right : ℕ)
  deriving DecidableEq

def Kind.record : Kind → GateRecord
  | .zero => .zero
  | .half p => .scale p (1/2)
  | .negative p => .scale p (-1)
  | .copy p => .scale p 1
  | .add l r => .add l r

def Kind.a : Kind → Bool
  | .add _ _ => true
  | _ => false

def Kind.b : Kind → Bool
  | .negative _ | .copy _ => true
  | _ => false

def Kind.c : Kind → Bool
  | .half _ | .copy _ => true
  | _ => false

def Kind.left : Kind → ℕ
  | .zero => 0
  | .half p | .negative p | .copy p => p
  | .add l _ => l

def Kind.right : Kind → ℕ
  | .add _ r => r
  | _ => 0

def Kind.leftWord (kind : Kind) (width : ℕ) : List Bool := SourceCircuit.fixedWidth width kind.left
def Kind.rightWord (kind : Kind) (width : ℕ) : List Bool := SourceCircuit.fixedWidth width kind.right

@[simp] theorem Kind.leftWord_length (kind : Kind) (width : ℕ) : (kind.leftWord width).length = width :=
  SourceCircuit.fixedWidth_length _ _
@[simp] theorem Kind.rightWord_length (kind : Kind) (width : ℕ) : (kind.rightWord width).length = width :=
  SourceCircuit.fixedWidth_length _ _

theorem Kind.gateBytes (kind : Kind) (width : ℕ) :
    SourceCircuit.gateBytes width kind.record =
      some (wire kind.a kind.b kind.c (kind.leftWord width) (kind.rightWord width)) := by
  cases kind <;> norm_num [SourceCircuit.gateBytes,Kind.record,Kind.a,Kind.b,Kind.c,
    Kind.leftWord,Kind.rightWord,Kind.left,Kind.right,wire,payload,
    SourceCircuit.zeroTag,SourceCircuit.halfTag,SourceCircuit.negativeTag,SourceCircuit.copyTag,
    SourceCircuit.additionTag,List.append_assoc]

/-- Successful archive encoding excludes every unsupported scale. -/
theorem exists_kind (width : ℕ) (g : GateRecord) (bytes : List Bool)
    (h : SourceCircuit.gateBytes width g = some bytes) : ∃ kind : Kind, kind.record = g := by
  cases g with
  | zero => exact ⟨.zero,rfl⟩
  | add l r => exact ⟨.add l r,rfl⟩
  | scale p w =>
    by_cases h1 : w = 1
    · subst w; exact ⟨.copy p,rfl⟩
    by_cases hh : w = 1/2
    · subst w; exact ⟨.half p,rfl⟩
    by_cases hn : w = -1
    · subst w; exact ⟨.negative p,rfl⟩
    have he : (none : Option (List Bool)) = some bytes := by
      simpa only [SourceCircuit.gateBytes,h1,hh,hn,↓reduceIte] using h
    cases he

theorem kind_wire_eq (width : ℕ) (kind : Kind) (bytes : List Bool)
    (h : SourceCircuit.gateBytes width kind.record = some bytes) :
    wire kind.a kind.b kind.c (kind.leftWord width) (kind.rightWord width) = bytes :=
  Option.some.inj ((kind.gateBytes width).symm.trans h)

theorem cursor_represents (pre suffix : List Bool) (origin : ℤ) :
    TapeRepresents (Increment.cursor pre suffix origin) suffix := by
  have h := advance_represents (BitTape.shifted (pre++suffix) origin) pre suffix
    (BitTape.shifted_represents _ _)
  exact h

theorem advance_cursor (pre word suffix : List Bool) (origin : ℤ) :
    advance (Increment.cursor pre (word++suffix) origin) word.length =
      Increment.cursor (pre++word) suffix origin := by
  simp [advance,Increment.cursor,List.append_assoc,Nat.cast_add,add_assoc]

end Maxwell.Cost.SparseEmission.ReadGate
