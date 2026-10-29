import Maxwell.Cost.ChildPermutation.Encoding

namespace Maxwell.Cost.ChildPermutation
open Maxwell.Logical.Routing
open Coloring.NumericSplit

/-- A computational binary factorization of a flat parent token space. -/
def unitRowIndex (m : ℕ) : Unit × Fin m ≃ Fin m where
  toFun := Prod.snd
  invFun i := ((),i)
  left_inv p := by rcases p with ⟨u,i⟩; cases u; rfl
  right_inv _ := rfl

/-- The split data exist for every numeric permutation, with the same
canonical flattened coloring used by the finite split program. -/
def Data.numeric (k : ℕ) (target : Equiv.Perm (Fin (2*2^k))) : Data k := by
  let index := halfIndex (unitRowIndex (2^k))
  let unflat := (index.trans target).trans index.symm
  let d := Data.ofBinarySplit k (unitRowIndex (2^k)) unflat
  have ht : d.target=target := by
    ext i
    simp [d,Data.ofBinarySplit,numericPerm,unflat,index,Equiv.trans_apply]
  have hc : d.colors=BinarySplit.colors k target := by
    change BinarySplit.colors k d.target=BinarySplit.colors k target
    rw [ht]
  exact ⟨target,BinarySplit.colors k target,d.left,d.right,
    fun i => by simpa only [ht,hc] using d.left_law i,
    fun i => by simpa only [ht,hc] using d.right_law i⟩

@[simp] theorem Data.numeric_target (k : ℕ) (target : Equiv.Perm (Fin (2*2^k))) :
    (Data.numeric k target).target=target := rfl

@[simp] theorem Data.numeric_colors (k : ℕ) (target : Equiv.Perm (Fin (2*2^k))) :
    (Data.numeric k target).colors=BinarySplit.colors k target := rfl

/-- Child arrays are determined by the parent and the stored split colors. -/
theorem Data.children_unique {k : ℕ} (a b : Data k) (ht : a.target=b.target) (hc : a.colors=b.colors) :
    a.left=b.left ∧ a.right=b.right := by
  constructor
  · ext i
    rw [a.left_law,b.left_law,ht,hc]
  · ext i
    rw [a.right_law,b.right_law,ht,hc]

end Maxwell.Cost.ChildPermutation
