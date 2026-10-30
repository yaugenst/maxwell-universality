import Maxwell.Continuum.SourceRoutingColorData

/-! The bottom-up numeric labels are exactly row-count times the logical
recursive column colors. Leaf labels are zero. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData
open Maxwell.Logical.Routing
open Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def childTarget (rows columns : ℕ) (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows)))
    (bit : Bool) : Equiv.Perm (Columns columns×Fin (2^rows)) :=
  reducedTarget target (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target) bit

def labels (rows columns : ℕ) (target : Equiv.Perm (Columns columns×Fin (2^rows))) :
    Vector (Fin (2^(columns+rows))) (2^(columns+rows)) := Vector.ofFn (fun i =>
  index rows columns ((recursiveColoring (Equiv.refl _) columns target).color ((index rows columns).symm i),
    ⟨0,by positivity⟩))

theorem label_value (rows columns : ℕ) (target : Equiv.Perm (Columns columns×Fin (2^rows)))
    (p : Columns columns×Fin (2^rows)) :
    ((labels rows columns target).get (index rows columns p)).val=
      2^rows*(columnsFinEquiv columns ((recursiveColoring (Equiv.refl _) columns target).color p)).val := by
  have he : (labels rows columns target).get (index rows columns p)=
      index rows columns ((recursiveColoring (Equiv.refl _) columns target).color p,⟨0,by positivity⟩) := by
    simp [labels,Vector.get,Fin.cast]
  rw [he]
  change 0+2^rows*(columnsFinEquiv columns ((recursiveColoring (Equiv.refl _) columns target).color p)).val=_
  omega

theorem labels_zero (rows : ℕ) (target : Equiv.Perm (Columns 0×Fin (2^rows)))
    (i : Fin (2^(0+rows))) : ((labels rows 0 target).get i).val=0 := by
  have h := label_value rows 0 target ((index rows 0).symm i)
  have zero (j : Fin (2^0)) : j.val=0 := by have := j.isLt; norm_num at this; omega
  simpa only [Equiv.apply_symm_apply,zero,mul_zero] using h

theorem proper_cast_color {C R : Type*} {a b : Equiv.Perm (C×R)} (h : a=b)
    (proper : Proper a) (p : C×R) : (h ▸ proper).color p=proper.color p := by
  subst b
  rfl

theorem storedProper_color {C R : Type*} {a : Equiv.Perm (C×R)} {n : ℕ}
    (idx : C×R≃Fin n) (proper : Proper a) (p : C×R) :
    (storedProper idx proper).color p=proper.color p := by
  simp [storedProper,Vector.get,Fin.cast]

theorem dependent_bool_choice {β : Bool→Type*} {α : Type*} (f : (b : Bool)→β b→α)
    (left : β false) (right : β true) (bit : Bool) :
    f bit (match bit with | false => left | true => right)=
      if bit then f true right else f false left := by
  cases bit <;> rfl

theorem recursive_color_succ (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows)))
    (p : Columns (columns+1)×Fin (2^rows)) :
    (recursiveColoring (Equiv.refl _) (columns+1) target).color p=
      ((binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target).color p,
        if (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target).color p then
          (recursiveColoring (Equiv.refl _) columns (childTarget rows columns target true)).color (tail p)
        else (recursiveColoring (Equiv.refl _) columns (childTarget rows columns target false)).color (tail p)) := by
  simp only [recursiveColoring,proper_cast_color,storedProper_color]
  have saved := storedPerm_eq (columnRowIndex (columns+1) (Equiv.refl (Fin (2^rows)))) target
  let raw (t : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) : Columns (columns+1) :=
    ((binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) t).color p,
      if (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) t).color p then
        (recursiveColoring (Equiv.refl _) columns (childTarget rows columns t true)).color (tail p)
      else (recursiveColoring (Equiv.refl _) columns (childTarget rows columns t false)).color (tail p))
  calc
    _ = raw (storedPerm (columnRowIndex (columns+1) (Equiv.refl _)) target) := by
      dsimp only [raw,childTarget]
      refine Prod.ext ?_ ?_
      · rfl
      · exact dependent_bool_choice (fun bit (proper : Proper
          (reducedTarget (storedPerm (columnRowIndex (columns+1) (Equiv.refl _)) target)
            (binarySplit (columnRowIndex (columns+1) (Equiv.refl _))
              (storedPerm (columnRowIndex (columns+1) (Equiv.refl _)) target)) bit)) =>
                proper.color (tail p)) _ _ _
    _ = raw target := congrArg raw saved
    _ = _ := rfl

def assembleData (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) : ColorAssemble.Data (columns+rows) :=
  ⟨(splitData rows columns target).colors,
    labels rows columns (childTarget rows columns target false),
    labels rows columns (childTarget rows columns target true)⟩

theorem child_index (rows columns : ℕ) (p : Columns (columns+1)×Fin (2^rows)) :
    ColorAssemble.childIndex (columns+rows) (halfIndex (index rows columns) p)=index rows columns (tail p) := by
  apply Fin.ext
  exact (halfIndex_tail_mod (index rows columns) p).symm

theorem columns_value_succ (columns : ℕ) (bit : Bool) (c : Columns columns) :
    (columnsFinEquiv (columns+1) (bit,c)).val=
      (columnsFinEquiv columns c).val+2^columns*bit.toNat := by
  cases bit <;> rfl

theorem assemble_value (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows)))
    (p : Columns (columns+1)×Fin (2^rows)) :
    ((assembleData rows columns target).value (halfIndex (index rows columns) p)).val=
      ((labels rows (columns+1) target).get (index rows (columns+1) p)).val := by
  rw [label_value,recursive_color_succ,columns_value_succ]
  change ((if (splitData rows columns target).colors.get (halfIndex (index rows columns) p) then
      labels rows columns (childTarget rows columns target true) else
      labels rows columns (childTarget rows columns target false)).get
        (ColorAssemble.childIndex (columns+rows) (halfIndex (index rows columns) p))).val+
      2^(columns+rows)*((splitData rows columns target).colors.get (halfIndex (index rows columns) p)).toNat=_
  rw [child_index,splitData_color]
  cases hbit : (binarySplit (columnRowIndex (columns+1) (Equiv.refl (Fin (2^rows)))) target).color p
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,label_value,Bool.toNat_false,
    Bool.toNat_true,mul_zero,mul_one,add_zero]
  rw [pow_add]
  ring

#print axioms recursive_color_succ
#print axioms assemble_value

end Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData
