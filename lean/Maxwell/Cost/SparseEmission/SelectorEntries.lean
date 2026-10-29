import Maxwell.Cost.SparseEmission.Encoding
import Mathlib.Data.List.OfFn

namespace Maxwell.Cost.SparseEmission

def selectorEntries (start : ℕ) : List ℕ → List Logical.RationalCode.Entry
  | [] => []
  | parent::rest => ⟨start,parent,1⟩ :: selectorEntries (start+1) rest

theorem selectorEntries_append (start : ℕ) (a b : List ℕ) :
    selectorEntries start (a++b) = selectorEntries start a ++ selectorEntries (start+a.length) b := by
  induction a generalizing start with
  | nil => simp [selectorEntries]
  | cons p a ih => simp [selectorEntries,ih,Nat.add_comm,Nat.add_left_comm]

@[simp] theorem selectorEntries_length (start : ℕ) (a : List ℕ) :
    (selectorEntries start a).length = a.length := by
  induction a generalizing start with
  | nil => rfl
  | cons p a ih => simp [selectorEntries,ih]

theorem selectorEntries_ofFn {n : ℕ} (f : Fin n → ℕ) (start : ℕ) :
    selectorEntries start (List.ofFn f) = List.ofFn (fun i : Fin n =>
      (⟨start+i.val,f i,1⟩ : Logical.RationalCode.Entry)) := by
  induction n generalizing start with
  | zero => simp [selectorEntries]
  | succ n ih =>
    simp only [List.ofFn_succ,selectorEntries,ih,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 2
    funext i
    congr 1
    omega

end Maxwell.Cost.SparseEmission
