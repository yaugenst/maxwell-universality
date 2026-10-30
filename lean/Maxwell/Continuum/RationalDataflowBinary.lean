import Maxwell.Continuum.RationalDataflowLayout

/-! Fixed arithmetic stages with shared logical registers and safe in-place updates. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

inductive BinaryOp where
  | add | sub | mul
  deriving DecidableEq, Repr

def BinaryOp.eval : BinaryOp → Parts → Parts → Parts
  | .add => Parts.add
  | .sub => Parts.sub
  | .mul => Parts.mul

def loadBinary (left right : ℕ) : List NatAssign.Instruction :=
  [.copy (positivePort left) 100,.copy (negativePort left) 101,
   .copy (denominatorPort left) 102,.copy (positivePort right) 103,
   .copy (negativePort right) 104,.copy (denominatorPort right) 105]

def clearTemporary : List NatAssign.Instruction :=
  [.literal 100 0,.literal 101 0,.literal 102 0,.literal 103 0,
   .literal 104 0,.literal 105 0,.literal 106 0]

def binaryBody (op : BinaryOp) (target : ℕ) : List NatAssign.Instruction :=
  let p := positivePort target
  let n := negativePort target
  let d := denominatorPort target
  match op with
  | .add =>
    [.copy 100 p,.multiply 105 p,.copy 103 106,.multiply 102 106,.add 106 p,
     .copy 101 n,.multiply 105 n,.copy 104 106,.multiply 102 106,.add 106 n,
     .copy 102 d,.multiply 105 d]
  | .sub =>
    [.copy 100 p,.multiply 105 p,.copy 104 106,.multiply 102 106,.add 106 p,
     .copy 101 n,.multiply 105 n,.copy 103 106,.multiply 102 106,.add 106 n,
     .copy 102 d,.multiply 105 d]
  | .mul =>
    [.copy 100 p,.multiply 103 p,.copy 101 106,.multiply 104 106,.add 106 p,
     .copy 100 n,.multiply 104 n,.copy 101 106,.multiply 103 106,.add 106 n,
     .copy 102 d,.multiply 105 d]

def binaryStage (op : BinaryOp) (target left right : ℕ) : List NatAssign.Instruction :=
  loadBinary left right ++ binaryBody op target ++ clearTemporary

@[simp] theorem positivePort_inj (i j : ℕ) : positivePort i=positivePort j ↔ i=j := by
  unfold positivePort
  omega
@[simp] theorem negativePort_inj (i j : ℕ) : negativePort i=negativePort j ↔ i=j := by
  unfold negativePort
  omega
@[simp] theorem denominatorPort_inj (i j : ℕ) : denominatorPort i=denominatorPort j ↔ i=j := by
  unfold denominatorPort
  omega
@[simp] theorem positive_ne_negative (i j : ℕ) : positivePort i≠negativePort j := by
  unfold positivePort negativePort
  omega
@[simp] theorem positive_ne_denominator (i j : ℕ) : positivePort i≠denominatorPort j := by
  unfold positivePort denominatorPort
  omega
@[simp] theorem negative_ne_positive (i j : ℕ) : negativePort i≠positivePort j :=
  (positive_ne_negative j i).symm
@[simp] theorem negative_ne_denominator (i j : ℕ) : negativePort i≠denominatorPort j := by
  unfold negativePort denominatorPort
  omega
@[simp] theorem denominator_ne_positive (i j : ℕ) : denominatorPort i≠positivePort j :=
  (positive_ne_denominator j i).symm
@[simp] theorem denominator_ne_negative (i j : ℕ) : denominatorPort i≠negativePort j :=
  (negative_ne_denominator j i).symm

theorem binaryStage_length (op : BinaryOp) (target left right : ℕ) :
    (binaryStage op target left right).length=25 := by
  cases op <;> rfl

theorem binaryStage_valid (S : Finset ℕ) (op : BinaryOp) (target left right : ℕ)
    (ht : target∈S) (hl : left∈S) (hr : right∈S) :
    ∀ a∈binaryStage op target left right, a.Valid (ids S) := by
  have ht' := cell_mem ht
  have hl' := cell_mem hl
  have hr' := cell_mem hr
  have hmem (i : ℕ) (hi : i∈temporaryPorts) : i∈ids S :=
    Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  have hlp := positivePort_ge left
  have hln := negativePort_ge left
  have hld := denominatorPort_ge left
  have hrp := positivePort_ge right
  have hrn := negativePort_ge right
  have hrd := denominatorPort_ge right
  have hp (i : ℕ) (hi : i∈S) : positivePort i∈ids S := cell_mem hi (by simp [cellPorts])
  have hn (i : ℕ) (hi : i∈S) : negativePort i∈ids S := cell_mem hi (by simp [cellPorts])
  have hd (i : ℕ) (hi : i∈S) : denominatorPort i∈ids S := cell_mem hi (by simp [cellPorts])
  cases op <;>
    simp (disch := omega) [binaryStage,loadBinary,binaryBody,clearTemporary,
      NatAssign.Instruction.Valid,hp _ ht,hn _ ht,hd _ ht,hp _ hl,hn _ hl,hd _ hl,
      hp _ hr,hn _ hr,hd _ hr,hmem 100 (by decide),hmem 101 (by decide),
      hmem 102 (by decide),hmem 103 (by decide),hmem 104 (by decide),
      hmem 105 (by decide),hmem 106 (by decide)] <;> omega

theorem binaryStage_literalWidth (op : BinaryOp) (target left right : ℕ) :
    ∀ a∈binaryStage op target left right, a.literalWidth=0 := by
  cases op <;> simp [binaryStage,loadBinary,binaryBody,clearTemporary,NatAssign.Instruction.literalWidth]

#print axioms binaryStage_valid

end Maxwell.Continuum.RationalDataflow
