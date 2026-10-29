import Maxwell.Cost.PhysicalMaterial.Membership.Offset
import Maxwell.Cost.IndexedAddress

namespace Maxwell.Cost.PhysicalMaterial.Membership
open Structured RationalAccumulator

def work : Finset ℕ := {0,1,2,3,290,291,292}

def Free (s : BitRAMState) : Prop :=
  Ready s ∧ Blank s 290 ∧ Blank s 291 ∧ Blank s 292

def Words (cell anchor : Fin 3 → ℕ) (s : BitRAMState) : Prop :=
  ∀ j, Word s (240+j.val) (cell j) ∧ Word s (294+j.val) (anchor j)

theorem Words.frame {cell anchor : Fin 3 → ℕ} {s t : BitRAMState}
    (h : Words cell anchor s) (f : BinaryPrecision.Frame work s t) : Words cell anchor t := by
  intro j
  have hj := j.isLt
  constructor
  · exact word_of_eq (f.tapes (240+j.val) (by simp [work]; omega)) (h j).1
  · exact word_of_eq (f.tapes (294+j.val) (by simp [work]; omega)) (h j).2

def coordinateCode (j : Fin 3) (delta : ℤ) : Code :=
  .seq (offsetCode (240+j.val) 290 (-delta).toNat)
    (.seq (offsetCode (294+j.val) 291 delta.toNat) equalCode)

def offsetSize (delta : ℤ) : ℕ := (-delta).toNat.bits.length+delta.toNat.bits.length+4

theorem signed_offset (x y : ℕ) (delta : ℤ) :
    x+(-delta).toNat = y+delta.toNat ↔ (x : ℤ) = (y : ℤ)+delta := by
  omega

set_option maxRecDepth 8192 in
theorem coordinate_executes (j : Fin 3) (delta : ℤ) (cell anchor : Fin 3 → ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Words cell anchor s.val) (hf : Free s.val) :
    ∃ cost t, cost ≤ 500*((cell j).bits.length+(anchor j).bits.length+offsetSize delta) ∧
      Executes input tape (coordinateCode j delta) cost s t ∧
      (t.val.registers 2 = true ↔ (cell j : ℤ) = (anchor j : ℤ)+delta) ∧
      Free t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  have hj := j.isLt
  obtain ⟨ac,a,hac,ea,aw,a292,ar,af⟩ := offset_executes (240+j.val) 290 (-delta).toNat
    (by omega) (Or.inl rfl) (by omega) (by omega) input tape (cell j) s (hw j).1 hf.2.1 hf.2.2.2 hf.1
  have af' : BinaryPrecision.Frame work s.val a.val := af.mono (by simp [offsetWork,work])
  obtain ⟨bc,b,hbc,eb,bw,b292,br,bf⟩ := offset_executes (294+j.val) 291 delta.toNat
    (by omega) (Or.inr rfl) (by omega) (by omega) input tape (anchor j) a
    (hw.frame af' j).2 (blank_of_eq (af.tapes 291 (by simp [offsetWork])) hf.2.2.1) a292 ar
  have bf' : BinaryPrecision.Frame work a.val b.val := bf.mono (by simp [offsetWork,work])
  have baw : Word b.val 290 (cell j+(-delta).toNat) :=
    word_of_eq (bf.tapes 290 (by simp [offsetWork])) aw
  obtain ⟨xo,hxo⟩ := baw
  obtain ⟨yo,hyo⟩ := bw
  obtain ⟨cc,t,hcc,ec,hbit,t290,t291,tf⟩ := equal_executes input tape
    (cell j+(-delta).toNat) (anchor j+delta.toNat) xo yo b hxo hyo
  have tf' : BinaryPrecision.Frame work b.val t.val := tf.mono (by decide)
  have hx := IndexedAddress.sum_length_le (cell j).bits (-delta).toNat.bits
  have hy := IndexedAddress.sum_length_le (anchor j).bits delta.toNat.bits
  simp only [addressValue_bits] at hx hy
  refine ⟨ac+(bc+cc),t,?_,ea.seq (eb.seq ec),hbit.trans (signed_offset _ _ _),?_,
    af'.trans (bf'.trans tf')⟩
  · unfold offsetSize
    omega
  · refine ⟨?_,⟨xo,t290⟩,⟨yo,t291⟩,blank_of_eq (tf.tapes 292 (by decide)) b292⟩
    intro i hi
    exact blank_of_eq (tf.tapes i (by simp; omega)) (br i hi)

end Maxwell.Cost.PhysicalMaterial.Membership
