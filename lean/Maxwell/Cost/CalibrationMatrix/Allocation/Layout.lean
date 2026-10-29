import Maxwell.Cost.CalibrationMatrix.Horner.Store

namespace Maxwell.Cost.CalibrationMatrix.Allocation

def matrixSpan (n width : ℕ) : ℕ := n*n*width
def vectorSpan (n width : ℕ) : ℕ := n*width
def denseBase (n width i : ℕ) : ℕ := 2*matrixSpan n width+i*vectorSpan n width
def sparseBase (n width capacity i : ℕ) : ℕ := denseBase n width 14+i*(capacity*width)
def memoryEnd (n width capacity : ℕ) : ℕ := sparseBase n width capacity 3

theorem dense_separated (n width : ℕ) (i j : Fin 14) (hne : i ≠ j) :
    IncidenceEncoding.Separated (denseBase n width i.val) (n*width)
      (denseBase n width j.val) (n*width) := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hji
  · left
    have hm := Nat.mul_le_mul_right (n*width) (show i.val+1 ≤ j.val by omega)
    dsimp [denseBase,vectorSpan]
    nlinarith only [hm]
  · right
    have hm := Nat.mul_le_mul_right (n*width) (show j.val+1 ≤ i.val by omega)
    dsimp [denseBase,vectorSpan]
    nlinarith only [hm]

theorem positive_separated (n width i : ℕ) :
    IncidenceEncoding.Separated 0 (n*n*width) (denseBase n width i) (n*width) := by
  left
  dsimp [denseBase,matrixSpan]
  omega

theorem negative_separated (n width i : ℕ) :
    IncidenceEncoding.Separated (matrixSpan n width) (n*n*width) (denseBase n width i) (n*width) := by
  left
  dsimp [denseBase,matrixSpan]
  omega

theorem sparse_dense_separated (n width capacity entries j : ℕ) (i : Fin 14) :
    IncidenceEncoding.Separated (sparseBase n width capacity j) (entries*width)
      (denseBase n width i.val) (n*width) := by
  right
  have hm := Nat.mul_le_mul_right (n*width) (show i.val+1 ≤ 14 by omega)
  dsimp [sparseBase,denseBase,vectorSpan]
  nlinarith only [hm,Nat.zero_le (j*(capacity*width))]

theorem sparse_separated (n width capacity entries : ℕ) (hlen : entries ≤ capacity)
    (i j : Fin 3) (hne : i ≠ j) :
    IncidenceEncoding.Separated (sparseBase n width capacity i.val) (entries*width)
      (sparseBase n width capacity j.val) (entries*width) := by
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hspan := Nat.mul_le_mul_right width hlen
  rcases Nat.lt_or_gt_of_ne hval with hij | hji
  · left
    have hm := Nat.mul_le_mul_right (capacity*width) (show i.val+1 ≤ j.val by omega)
    dsimp [sparseBase]
    nlinarith only [hm,hspan]
  · right
    have hm := Nat.mul_le_mul_right (capacity*width) (show j.val+1 ≤ i.val by omega)
    dsimp [sparseBase]
    nlinarith only [hm,hspan]

/-- The left source occupies the last two dense intervals, beyond all
twelve changing inverse-workspace arrays. -/
theorem left_separated (n width : ℕ) (i : Fin 12) :
    IncidenceEncoding.Separated (denseBase n width 12) (n*width)
      (denseBase n width i.val) (n*width) ∧
    IncidenceEncoding.Separated (denseBase n width 13) (n*width)
      (denseBase n width i.val) (n*width) :=
  ⟨dense_separated n width 12 ⟨i.val,by omega⟩ (by
      intro h;have he := congrArg Fin.val h;change 12 = i.val at he;omega),
    dense_separated n width 13 ⟨i.val,by omega⟩ (by
      intro h;have he := congrArg Fin.val h;change 13 = i.val at he;omega)⟩

end Maxwell.Cost.CalibrationMatrix.Allocation
