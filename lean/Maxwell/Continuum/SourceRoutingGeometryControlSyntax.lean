import Maxwell.Continuum.SourceRoutingGeometryDivisionBounds
import Maxwell.Continuum.RationalDataflowIntegerEmit
import Maxwell.Cost.PhysicalMaterial.FixedSubtract

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

inductive Control where
  | done
  | assign (instruction : NatAssign.Instruction) (rest : Control)
  | divide (source divisor quotient remainder : ℕ) (rest : Control)
  | decrement (target : ℕ) (rest : Control)
  | positive (source : ℕ) (yes no : Control)

def Control.steps : Control→ℕ
  | .done => 0
  | .assign _ rest | .divide _ _ _ _ rest | .decrement _ rest => 1+rest.steps
  | .positive _ yes no => 1+max yes.steps no.steps

def positiveState (source : ℕ) (s : Store) : Store := Store.ofState {s.val with
  registers:=Function.update (Function.update s.val.registers 24 ((s.val.tapes source).read.getD false))
    23 ((s.val.tapes source).read.isSome)}

theorem positive_executes (source : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.atom (.readTape source 24 23)) 3 s (positiveState source s) := by
  apply Executes.atom (extra:=1) (t:={s.val.setRegister 24 ((s.val.tapes source).read.getD false) with
    registers:=Function.update (Function.update s.val.registers 24 ((s.val.tapes source).read.getD false))
      23 ((s.val.tapes source).read.isSome)})
  · simp [BitRAM.next,s.property]
  · simp [BitRAMState.setRegister,s.property]

theorem positive_flag (source n : ℕ) (s : Store) (word : Word s.val source n) :
    (positiveState source s).val.registers 23=decide (0<n) :=
  Maxwell.Continuum.RationalDataflow.IntegerEmit.word_present word

theorem positive_frame (source : ℕ) (s : Store) : BinaryPrecision.Frame work s.val (positiveState source s).val :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

def Control.code : Control→Code
  | .done => .skip
  | .assign a rest => .seq (NatAssign.code [a]) rest.code
  | .divide s d q r rest => .seq (divisionCode s d q r) rest.code
  | .decrement target rest => .seq (PhysicalMaterial.FixedSubtract.code target 1) rest.code
  | .positive source yes no => .seq (.atom (.readTape source 24 23)) (.branch 23 yes.code no.code)

def Control.evaluate : Control→(ℕ→ℕ)→(ℕ→ℕ)
  | .done,v => v
  | .assign a rest,v => rest.evaluate (a.update v)
  | .divide s d q r rest,v => rest.evaluate (divided v s d q r)
  | .decrement target rest,v => rest.evaluate (Function.update v target (v target-1))
  | .positive source yes no,v => if 0<v source then yes.evaluate v else no.evaluate v

def Control.Valid : Control→Prop
  | .done => True
  | .assign a rest => a.Valid controls ∧ rest.Valid
  | .divide s d q r rest => s∈controls ∧ d∈controls ∧ q∈controls ∧ r∈controls ∧ q≠r ∧ rest.Valid
  | .decrement target rest => target∈controls ∧ rest.Valid
  | .positive source yes no => source∈controls ∧ yes.Valid ∧ no.Valid

def Control.Literals (B : ℕ) : Control→Prop
  | .done => True
  | .assign a rest => a.literalWidth ≤ B ∧ rest.Literals B
  | .divide _ _ _ _ rest | .decrement _ rest => rest.Literals B
  | .positive _ yes no => yes.Literals B ∧ no.Literals B

def Control.Admissible : Control→(ℕ→ℕ)→Prop
  | .done,_ => True
  | .assign a rest,v => rest.Admissible (a.update v)
  | .divide s d q r rest,v => 0<v d ∧ rest.Admissible (divided v s d q r)
  | .decrement target rest,v => 0<v target ∧ rest.Admissible (Function.update v target (v target-1))
  | .positive source yes no,v => if 0<v source then yes.Admissible v else no.Admissible v

theorem Control.Literals.mono {B C : ℕ} {c : Control} (h : c.Literals B) (le : B ≤ C) : c.Literals C := by
  induction c with
  | done => trivial
  | assign a rest ih => exact ⟨h.1.trans le,ih h.2⟩
  | divide _ _ _ _ rest ih => exact ih h
  | decrement _ rest ih => exact ih h
  | positive _ yes no iy ino => exact ⟨iy h.1,ino h.2⟩

theorem instruction_valid {a : NatAssign.Instruction} (h : a.Valid controls) : a.Valid ids := by
  cases a <;> simp only [NatAssign.Instruction.Valid] at h ⊢
  · exact Finset.mem_union_left _ h
  all_goals exact ⟨Finset.mem_union_left _ h.1,Finset.mem_union_left _ h.2.1,h.2.2⟩

theorem instruction_zero {a : NatAssign.Instruction} (h : a.Valid controls) (v : ℕ→ℕ)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,a.update v j=0 := by
  have target : a.target∈controls := by
    cases a <;> simp only [NatAssign.Instruction.Valid,NatAssign.Instruction.target] at h ⊢
    · exact h
    all_goals exact h.2.1
  intro j hj
  have different : j≠a.target := by
    simp only [controls,Finset.mem_Icc] at target
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
      Finset.mem_insert,Finset.mem_singleton] at hj
    omega
  simpa only [NatAssign.Instruction.update,Function.update_of_ne different] using zero j hj

def Control.prepend (instructions : List NatAssign.Instruction) (rest : Control) : Control :=
  instructions.foldr .assign rest

#print axioms positive_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
