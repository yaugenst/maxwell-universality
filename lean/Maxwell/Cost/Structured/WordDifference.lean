import Maxwell.Cost.Structured.WordMagnitude

/-! Nonnegative subtraction is a specialization of the shared signed
magnitude routine; both entry points execute exactly the same program. -/
namespace Maxwell.Cost.Structured.WordDifference
open RationalAccumulator (Word Blank)

def code (left right target : ℕ) : Code := WordMagnitude.code left right target

theorem magnitude_eq (x y : ℕ) (ordered : y ≤ x) :
    addressValue (SignedDifference.magnitude x.bits y.bits)=x-y := by
  rw [IntegerNormSquare.magnitude_eq]
  unfold IntegerNormSquare.magnitude
  omega

theorem difference_length (x y : ℕ) (ordered : y ≤ x) :
    (x-y).bits.length ≤ max x.bits.length y.bits.length+1 := by
  have eq : IntegerNormSquare.magnitude x y=x-y := by
    unfold IntegerNormSquare.magnitude
    omega
  simpa only [eq] using IntegerNormSquare.magnitude_bits_length_le x y

theorem executes (left right target : ℕ) (hl : 4 ≤ left) (hr : 4 ≤ right)
    (ht : 4 ≤ target) (input : List Bool) (tape : ℕ→Bool) (x y : ℕ) (ordered : y ≤ x)
    (s : Store) (leftWord : Word s.val left x) (rightWord : Word s.val right y)
    (targetBlank : Blank s.val target) (scratch : ∀i,i<4→Blank s.val i) :
    ∃cost t,Executes input tape (code left right target) cost s t ∧
      cost ≤ 300*(x.bits.length+y.bits.length+4) ∧ Word t.val target (x-y) ∧
      (∀i,i<4→Blank t.val i) ∧ BinaryPrecision.Frame {0,1,2,target} s.val t.val := by
  obtain ⟨cost,t,ex,hc,word,blank,frame,_⟩:=WordMagnitude.executes left right target hl hr ht
    input tape x y s leftWord rightWord targetBlank scratch
  have eq : IntegerNormSquare.magnitude x y=x-y := by
    unfold IntegerNormSquare.magnitude
    omega
  exact ⟨cost,t,ex,hc,by simpa only [eq] using word,blank,frame⟩

#print axioms executes
end Maxwell.Cost.Structured.WordDifference
