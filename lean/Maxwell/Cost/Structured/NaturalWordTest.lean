import Maxwell.Cost.Structured.BooleanWord

/-! A canonical natural word is nonzero exactly when its first cell exists.
The present-bit read charges a real instruction and leaves every tape intact. -/
namespace Maxwell.Cost.Structured.NaturalWordTest

def code (source flag : ℕ) : Code := .atom (.readTape source flag flag)

theorem executes (source flag n : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (word : RationalAccumulator.Word s.val source n) :
    ∃t,Executes input tape (code source flag) 3 s t ∧
      t.val.registers flag=decide (0<n) ∧ BinaryPrecision.Frame ∅ s.val t.val := by
  let t:=Store.ofState (readTapeState s.val source flag flag)
  have execution : Executes input tape (code source flag) 3 s t := by
    apply Executes.atom (extra:=1)
    · simp [BitRAM.next,s.property,readTapeState]
    · simp [readTapeState,s.property]
  have present : n.bits.head?.isSome=decide (0<n) := by
    cases bits : n.bits with
    | nil =>
      have zero : n=0 := by simpa only [bits,addressValue] using (addressValue_bits n).symm
      simp [zero]
    | cons bit rest =>
      have positive : 0<n := by
        by_contra contrary
        have zero : n=0 := by omega
        simp [zero] at bits
      simp [positive]
  obtain ⟨origin,stored⟩:=word
  have read : (s.val.tapes source).read=n.bits.head? := by
    rw [stored]
    exact (BitTape.shifted_represents n.bits origin).read
  exact ⟨t,execution,by simpa only [t,Store.ofState,readTapeState,Function.update_self,read] using present,
    ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩⟩

#print axioms executes
end Maxwell.Cost.Structured.NaturalWordTest
