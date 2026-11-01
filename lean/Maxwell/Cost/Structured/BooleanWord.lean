import Maxwell.Cost.RationalAccumulator.Bank
import Maxwell.Cost.Structured.Primitive
import Maxwell.Cost.BinaryPrecision

/-! Read a stored zero-or-one natural into a branch register without moving
its tape head or changing any stored data. -/
namespace Maxwell.Cost.Structured.BooleanWord

def code (source result present : ℕ) : Code := .atom (.readTape source result present)

theorem executes (source result present : ℕ) (distinct : result≠present) (value : Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (word : RationalAccumulator.Word s.val source (if value then 1 else 0)) :
    ∃t,Executes input tape (code source result present) 3 s t ∧
      t.val.registers result=value ∧ BinaryPrecision.Frame ∅ s.val t.val := by
  let t:=Store.ofState (readTapeState s.val source result present)
  have execution : Executes input tape (code source result present) 3 s t := by
    apply Executes.atom (extra:=1)
    · simp [BitRAM.next,s.property,readTapeState]
    · simp [readTapeState,s.property]
  refine ⟨t,execution,?_,⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩
  obtain ⟨origin,stored⟩:=word
  cases value <;>
    simp [t,Store.ofState,readTapeState,distinct,stored,BitTape.read,BitTape.shifted]

#print axioms executes
end Maxwell.Cost.Structured.BooleanWord
