import Maxwell.Continuum.RationalDataflowBinary

/-! Exact shared-register semantics, proved a fixed arithmetic stage at a time. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem values_append (xs ys : List NatAssign.Instruction) (v : ℕ→ℕ) :
    NatAssign.values (xs++ys) v=NatAssign.values ys (NatAssign.values xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (x.update v)

def writeParts (v : ℕ→ℕ) (target : ℕ) (x : Parts) : ℕ→ℕ :=
  Function.update (Function.update (Function.update v (positivePort target) x.positive)
    (negativePort target) x.negative) (denominatorPort target) x.denominator

theorem writeParts_dataValues (v : ℕ→Parts) (target : ℕ) (x : Parts) :
    writeParts (dataValues v) target x=dataValues (Function.update v target x) := by
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  ext i
  by_cases hs : i<1000
  · simp (disch := omega) [writeParts,Function.update_of_ne,dataValues_small v hs,
      dataValues_small _ hs]
  · have hr : i=positivePort ((i-1000)/3) ∨ i=negativePort ((i-1000)/3) ∨
        i=denominatorPort ((i-1000)/3) := by
      unfold positivePort negativePort denominatorPort
      omega
    rcases hr with he | he | he
    all_goals
      rw [he]
      generalize (i-1000)/3=r
      by_cases hrt : r=target
      · subst r; simp [writeParts]
      · simp [writeParts,hrt]

def loadedValues (v : ℕ→Parts) (left right : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (dataValues v) 100 (v left).positive) 101 (v left).negative)
      102 (v left).denominator) 103 (v right).positive) 104 (v right).negative)
        105 (v right).denominator

theorem loadBinary_values (v : ℕ→Parts) (left right : ℕ) :
    NatAssign.values (loadBinary left right) (dataValues v)=loadedValues v left right := by
  have hlp := positivePort_ge left
  have hln := negativePort_ge left
  have hld := denominatorPort_ge left
  have hrp := positivePort_ge right
  have hrn := negativePort_ge right
  have hrd := denominatorPort_ge right
  simp (disch := omega) [loadBinary,loadedValues,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

def sumProducts (target a b c d : ℕ) : List NatAssign.Instruction :=
  [.copy a target,.multiply b target,.copy c 106,.multiply d 106,.add 106 target]

theorem sumProducts_values (v : ℕ→ℕ) (target a b c d : ℕ)
    (ht : 1000≤target) (_ha : a<106) (hb : b<106) (hc : c<106) (hd : d<106) :
    NatAssign.values (sumProducts target a b c d) v=
      Function.update (Function.update v 106 (v d*v c)) target (v d*v c+v b*v a) := by
  ext i
  by_cases hi : i=target
  · subst i
    simp (disch := omega) [sumProducts,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value]
  · by_cases h106 : i=106
    · subst i
      simp (disch := omega) [sumProducts,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value]
    · simp (disch := omega) [sumProducts,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem product_values (v : ℕ→ℕ) (target a b : ℕ)
    (ht : 1000≤target) (_ha : a<106) (hb : b<106) :
    NatAssign.values [.copy a target,.multiply b target] v=
      Function.update v target (v b*v a) := by
  simp (disch := omega) [NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

def bodyExtra (op : BinaryOp) (x y : Parts) : ℕ :=
  match op with
  | .add => x.denominator*y.negative
  | .sub => x.denominator*y.positive
  | .mul => y.positive*x.negative

theorem binaryBody_values (op : BinaryOp) (target left right : ℕ) (v : ℕ→Parts) :
    NatAssign.values (binaryBody op target) (loadedValues v left right)=
      writeParts (Function.update (loadedValues v left right) 106 (bodyExtra op (v left) (v right)))
        target (op.eval (v left) (v right)) := by
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  cases op with
  | add =>
    change NatAssign.values (sumProducts (positivePort target) 100 105 103 102 ++
      sumProducts (negativePort target) 101 105 104 102 ++
      [.copy 102 (denominatorPort target),.multiply 105 (denominatorPort target)]) _ = _
    rw [values_append,values_append,sumProducts_values _ _ _ _ _ _ htp (by decide) (by decide) (by decide) (by decide),
      sumProducts_values _ _ _ _ _ _ htn (by decide) (by decide) (by decide) (by decide),
      product_values _ _ _ _ htd (by decide) (by decide)]
    ext i
    by_cases hp : i=positivePort target
    · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.add,Nat.add_comm,Nat.mul_comm]
    · by_cases hn : i=negativePort target
      · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.add,Nat.add_comm,Nat.mul_comm]
      · by_cases hd : i=denominatorPort target
        · subst i; simp (disch := omega) [writeParts,loadedValues,bodyExtra,BinaryOp.eval,Parts.add,Nat.add_comm,Nat.mul_comm]
        · simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra]
  | sub =>
    change NatAssign.values (sumProducts (positivePort target) 100 105 104 102 ++
      sumProducts (negativePort target) 101 105 103 102 ++
      [.copy 102 (denominatorPort target),.multiply 105 (denominatorPort target)]) _ = _
    rw [values_append,values_append,sumProducts_values _ _ _ _ _ _ htp (by decide) (by decide) (by decide) (by decide),
      sumProducts_values _ _ _ _ _ _ htn (by decide) (by decide) (by decide) (by decide),
      product_values _ _ _ _ htd (by decide) (by decide)]
    ext i
    by_cases hp : i=positivePort target
    · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.sub,Nat.add_comm,Nat.mul_comm]
    · by_cases hn : i=negativePort target
      · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.sub,Nat.add_comm,Nat.mul_comm]
      · by_cases hd : i=denominatorPort target
        · subst i; simp (disch := omega) [writeParts,loadedValues,bodyExtra,BinaryOp.eval,Parts.sub,Nat.add_comm,Nat.mul_comm]
        · simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra]
  | mul =>
    change NatAssign.values (sumProducts (positivePort target) 100 103 101 104 ++
      sumProducts (negativePort target) 100 104 101 103 ++
      [.copy 102 (denominatorPort target),.multiply 105 (denominatorPort target)]) _ = _
    rw [values_append,values_append,sumProducts_values _ _ _ _ _ _ htp (by decide) (by decide) (by decide) (by decide),
      sumProducts_values _ _ _ _ _ _ htn (by decide) (by decide) (by decide) (by decide),
      product_values _ _ _ _ htd (by decide) (by decide)]
    ext i
    by_cases hp : i=positivePort target
    · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.mul,Nat.add_comm,Nat.mul_comm]
    · by_cases hn : i=negativePort target
      · subst i; simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra,BinaryOp.eval,Parts.mul,Nat.add_comm,Nat.mul_comm]
      · by_cases hd : i=denominatorPort target
        · subst i; simp (disch := omega) [writeParts,loadedValues,bodyExtra,BinaryOp.eval,Parts.mul,Nat.add_comm,Nat.mul_comm]
        · simp (disch := omega) [writeParts,loadedValues,Function.update_apply,bodyExtra]

theorem clearTemporary_values (v : ℕ→ℕ) :
    NatAssign.values clearTemporary v=
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v 100 0) 101 0) 102 0) 103 0) 104 0) 105 0) 106 0 := rfl

theorem binaryStage_values (op : BinaryOp) (target left right : ℕ) (v : ℕ→Parts) :
    NatAssign.values (binaryStage op target left right) (dataValues v)=
      dataValues (Function.update v target (op.eval (v left) (v right))) := by
  rw [binaryStage,values_append,values_append,loadBinary_values,binaryBody_values,
    clearTemporary_values,←writeParts_dataValues]
  have htp := positivePort_ge target
  have htn := negativePort_ge target
  have htd := denominatorPort_ge target
  ext i
  by_cases hs : i<1000
  · simp (disch := omega) [writeParts,loadedValues,Function.update_apply,dataValues_small v hs]
  · simp (disch := omega) [writeParts,loadedValues,Function.update_apply]

#print axioms binaryStage_values

end Maxwell.Continuum.RationalDataflow
