import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.EmitLiteral
open Structured

/-- The bit list is a compile-time constant. Variable-length data must use
an actual tape scan or counted loop rather than this constructor. -/
def code (register : ℕ) : List Bool → Code
  | [] => .skip
  | b :: bs => .seq (Code.atom (.literal register b))
      (.seq (Code.atom (.output register)) (code register bs))

def emitOne (register : ℕ) (b : Bool) (s : Store) : Store :=
  Store.ofState {s.val with
    registers := Function.update s.val.registers register b
    output := b :: s.val.output}

def finish (register : ℕ) : List Bool → Store → Store
  | [], s => s
  | b :: bs, s => finish register bs (emitOne register b s)

theorem executes (register : ℕ) (bits : List Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (s : Store) :
    Executes input randomTape (code register bits) (4*bits.length+1) s
      (finish register bits s) := by
  induction bits generalizing s with
  | nil => exact Executes.skip s
  | cons b bs ih =>
    have hl := Executes.literal input randomTape s register b
    let t := Store.ofState (s.val.setRegister register b)
    have ho := Executes.output input randomTape t register
    have ht : Store.ofState {t.val with pc := 1, output := t.val.registers register :: t.val.output} =
        emitOne register b s := by simp [t, Store.ofState, BitRAMState.setRegister, emitOne]
    rw [ht] at ho
    have he := hl.seq (ho.seq (ih (emitOne register b s)))
    have hcost : 4*(b::bs).length+1 = 2+(2+(4*bs.length+1)) := by
      simp only [List.length_cons]
      omega
    rw [hcost]
    exact he

theorem finish_output (register : ℕ) (bits : List Bool) (s : Store) :
    (finish register bits s).val.output = bits.reverse ++ s.val.output := by
  induction bits generalizing s with
  | nil => simp [finish]
  | cons b bs ih => simp [finish, ih, emitOne, Store.ofState, List.append_assoc]

def Frame (register : ℕ) (s t : Store) : Prop :=
  t.val.address = s.val.address ∧ t.val.inputHead = s.val.inputHead ∧
  t.val.memory = s.val.memory ∧ t.val.randomCursor = s.val.randomCursor ∧
  t.val.tapes = s.val.tapes ∧ ∀ i, i ≠ register → t.val.registers i = s.val.registers i

theorem finish_frame (register : ℕ) (bits : List Bool) (s : Store) :
    Frame register s (finish register bits s) := by
  induction bits generalizing s with
  | nil => simp [finish, Frame]
  | cons b bs ih =>
    have h := ih (emitOne register b s)
    rcases h with ⟨ha, hi, hm, hr, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ht, ?_⟩
    intro i hne
    simpa [finish, emitOne, Store.ofState, hne] using hg i hne

end Maxwell.Cost.EmitLiteral
