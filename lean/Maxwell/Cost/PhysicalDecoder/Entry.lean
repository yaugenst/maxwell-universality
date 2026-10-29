import Maxwell.Cost.PhysicalDecoder.Samples
import Maxwell.Cost.PhysicalDecoder.Coefficient

namespace Maxwell.Cost.PhysicalDecoder.Entry
open Structured RationalAccumulator

def work : Finset ℕ := Samples.work ∪ Coefficient.work

structure Frame (s t : BitRAMState) : Prop where
  address : t.address=s.address
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  tapes : ∀ i ∉ work,t.tapes i=s.tapes i

/-- The local index is a fixed prototype index, while the row base and all
rational factors are actual runtime words. Tape358 contains one sign bit. -/
def code (localIndex : ℕ) : Code := .seq (Samples.indexCode 345 (localIndex : ℤ))
  (.seq (.atom (.readTape 358 23 29)) Coefficient.code)

def costBound (localIndex B : ℕ) : ℕ :=
  Samples.coordinateFactor (localIndex : ℤ)*(B+1)+3+Coefficient.costBound B

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem executes (localIndex rowBase : ℕ) (x : Arithmetic.Data) (negative : Bool) (B : ℕ)
    (hb : rowBase.bits.length ≤ B) (hv : Arithmetic.Valid x) (hB : Arithmetic.Bounded x B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Word s.val 345 rowBase) (hsg : BankArray.Word s.val 358 [negative])
    (hs : Coefficient.Ready x s) (hz : Blank s.val 343) (h292 : Blank s.val 292)
    (hr : PhysicalMaterial.Scatter.Ready s.val) :
    ∃ cost t, cost ≤ costBound localIndex B ∧ Executes input tape (code localIndex) cost s t ∧
      t.val.output=(Codec.nat (rowBase+localIndex)++Codec.rat (Arithmetic.fraction x negative)).reverse++s.val.output ∧
      Coefficient.Ready x t ∧ Blank t.val 343 ∧ Blank t.val 292 ∧
      PhysicalMaterial.Scatter.Ready t.val ∧ Frame s.val t.val := by
  obtain ⟨c,a,hc,ea,ao,az,a292,ar,af⟩ := Samples.index_executes 345 (by decide) (by decide)
    (localIndex:ℤ) rowBase B hb (by omega) input tape s hw hz h292 hr
  have ac : Coefficient.Ready x a := by
    refine ⟨?_,?_⟩
    · intro i
      exact word_of_eq (af.tapes (350+i.val) (by have := i.isLt; simp only [Samples.work,
        Finset.mem_insert,Finset.mem_singleton,not_or]; omega)) (hs.words i)
    · intro i hi
      by_cases hsmall : i<10
      · exact ar i hsmall
      · apply blank_of_eq (af.tapes i ?_) (hs.blank i hi)
        simp only [Coefficient.work,Arithmetic.work,PhysicalMaterial.ArithmeticBank.work,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
        simp only [Samples.work,Finset.mem_insert,Finset.mem_singleton,not_or]
        omega
  have asg : BankArray.Word a.val 358 [negative] := BankArray.word_of_eq (af.tapes 358 (by decide)) hsg
  let b := Store.ofState (readTapeState a.val 358 23 29)
  have eb : Executes input tape (.atom (.readTape 358 23 29)) 3 a b := by
    apply Executes.atom (extra := 1)
    · simp [BitRAM.next,a.property,readTapeState]
    · simp [readTapeState,a.property]
  have bs : b.val.registers 23=negative := by
    obtain ⟨origin,ho⟩ := asg
    simp [b,Store.ofState,readTapeState,ho,BitTape.shifted,BitTape.read]
  have bc : Coefficient.Ready x b := ⟨ac.words,ac.blank⟩
  obtain ⟨d,t,hd,et,tout,tc,tf⟩ := Coefficient.executes x negative B hv hB input tape b bc bs
  have kept (i : ℕ) (hi : i ∉ Coefficient.work) : t.val.tapes i=a.val.tapes i := tf.tapes i hi
  refine ⟨c+(3+d),t,by unfold costBound; omega,ea.seq (eb.seq et),?_,tc,
    blank_of_eq (kept 343 (by decide)) az,blank_of_eq (kept 292 (by decide)) a292,?_,?_⟩
  · rw [tout]
    change (Codec.rat _).reverse++a.val.output = _
    rw [ao]
    have he : ((rowBase:ℤ)+(localIndex:ℤ)).toNat=rowBase+localIndex := by omega
    rw [he,List.reverse_append,List.append_assoc]
  · intro i hi
    by_cases hsmall : i<5
    · exact tc.blank i (by interval_cases i <;> decide)
    · exact blank_of_eq (kept i (by
        interval_cases i <;> decide)) (ar i hi)
  · refine ⟨tf.address.trans af.address,tf.memory.trans af.memory,
      tf.inputHead.trans af.inputHead,tf.randomCursor.trans af.randomCursor,?_⟩
    intro i hi
    have hi' : i ∉ Samples.work ∧ i ∉ Coefficient.work := by simpa only [work,Finset.mem_union,not_or] using hi
    exact (kept i hi'.2).trans (af.tapes i hi'.1)

end Maxwell.Cost.PhysicalDecoder.Entry
