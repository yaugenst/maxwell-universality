import Maxwell.Cost.ChildPermutation.Encoding
import Maxwell.Cost.ColorAssemble.Encoding

/-! Numeric split data agree with the deterministic logical routing tree.
Index casts change finite types, never the represented integer coordinates. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData
open Maxwell.Logical.Routing
open Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def index (rows columns : ℕ) : Columns columns×Fin (2^rows) ≃ Fin (2^(columns+rows)) :=
  (columnRowIndex columns (Equiv.refl _)).trans (finCongr (pow_add 2 columns rows).symm)

theorem parent_size (rows columns : ℕ) : 2*2^(columns+rows)=2^(columns+1+rows) := by
  rw [show columns+1+rows=(columns+rows)+1 by omega,pow_succ']

theorem index_succ (rows columns : ℕ) :
    index rows (columns+1)=(halfIndex (index rows columns)).trans (finCongr (parent_size rows columns)) := by
  ext p
  have hh := columnRowIndex_succ columns (Equiv.refl (Fin (2^rows))) p
  have hv := halfIndex_val (columnRowIndex columns (Equiv.refl (Fin (2^rows)))) p
  have hh' := hh.trans hv
  calc
    _ = (columnRowIndex (columns+1) (Equiv.refl (Fin (2^rows))) p).val := rfl
    _ = (columnRowIndex columns (Equiv.refl (Fin (2^rows))) (tail p)).val+
        (2^columns*2^rows)*(finTwoEquiv.symm p.1.1).val := hh'
    _ = (index rows columns (tail p)).val+2^(columns+rows)*(finTwoEquiv.symm p.1.1).val := by
      exact congrArg₂ (fun a b : ℕ => a+b) rfl
        (congrArg (fun a : ℕ => a*(finTwoEquiv.symm p.1.1).val) (pow_add 2 columns rows).symm)
    _ = _ := (halfIndex_val (index rows columns) p).symm

theorem binarySplit_cast {C R : Type*} [Fintype C] [Fintype R]
    {a b : ℕ} (h : a=b) (idx : BinaryToken C R ≃ Fin a) (target : Equiv.Perm (BinaryToken C R)) :
    binarySplit (idx.trans (finCongr h)) target=binarySplit idx target := by
  subst b
  have he : idx.trans (finCongr rfl)=idx := by ext p; rfl
  rw [he]

theorem split_eq (rows columns : ℕ) (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) :
    binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target=
      binarySplit (halfIndex (index rows columns)) target := by
  have hh := binarySplit_cast (pow_add 2 (columns+1) rows).symm
    (columnRowIndex (columns+1) (Equiv.refl (Fin (2^rows)))) target
  change binarySplit (index rows (columns+1)) target=_ at hh
  rw [index_succ] at hh
  exact hh.symm.trans (binarySplit_cast (parent_size rows columns) (halfIndex (index rows columns)) target)

def splitData (rows columns : ℕ) (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) :
    ChildPermutation.Data (columns+rows) :=
  ChildPermutation.Data.ofBinarySplit (columns+rows) (index rows columns) target

theorem splitData_colors (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) :
    (splitData rows columns target).colors=
      BinarySplit.colors (columns+rows) (splitData rows columns target).target := rfl

theorem splitData_left (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) :
    (splitData rows columns target).left=numericPerm (index rows columns)
      (reducedTarget target (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target) false) := by
  rw [split_eq]
  rfl

theorem splitData_right (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) :
    (splitData rows columns target).right=numericPerm (index rows columns)
      (reducedTarget target (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target) true) := by
  rw [split_eq]
  rfl

theorem splitData_color (rows columns : ℕ)
    (target : Equiv.Perm (Columns (columns+1)×Fin (2^rows))) (p : Columns (columns+1)×Fin (2^rows)) :
    (splitData rows columns target).colors.get (halfIndex (index rows columns) p)=
      (binarySplit (columnRowIndex (columns+1) (Equiv.refl _)) target).color p := by
  change (BinarySplit.colors (columns+rows) (numericPerm (halfIndex (index rows columns)) target)).get _=_
  rw [BinarySplit.colors_eq_binarySplit (columns+rows) (index rows columns) target,split_eq]
  simp [Vector.get,Fin.cast]
  exact congrArg (binarySplit (halfIndex (index rows columns)) target).color
    ((halfIndex (index rows columns)).symm_apply_apply p)

#print axioms split_eq
#print axioms splitData_color

end Maxwell.Cost.RoutingPorts.Complete.Tree.ColorData
