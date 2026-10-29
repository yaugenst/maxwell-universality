import Maxwell.Cost.RealSparseOrder.Buffer
import Mathlib.Data.List.Sort

namespace Maxwell.Cost.RealSparseOrder

/-- Canonical row-major comparison; real coefficients play no role in sorting. -/
def KeyLE (a b : SparseEntry) : Prop := a.row < b.row ∨ (a.row=b.row ∧ a.column≤b.column)

instance : DecidableRel KeyLE := fun a b => inferInstanceAs
  (Decidable (a.row < b.row ∨ (a.row=b.row ∧ a.column≤b.column)))

theorem keyLE_refl (a : SparseEntry) : KeyLE a a := Or.inr ⟨rfl,le_rfl⟩

theorem keyLE_trans (a b c : SparseEntry) (h : KeyLE a b) (k : KeyLE b c) : KeyLE a c := by
  rcases h with h | ⟨h,hc⟩ <;> rcases k with k | ⟨k,kc⟩
  · exact Or.inl (lt_trans h k)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h.trans k,le_trans hc kc⟩

theorem keyLE_total (a b : SparseEntry) : KeyLE a b ∨ KeyLE b a := by
  by_cases h : a.row < b.row
  · exact Or.inl (Or.inl h)
  by_cases k : b.row < a.row
  · exact Or.inr (Or.inl k)
  have he : a.row=b.row := by omega
  rcases le_total a.column b.column with hc | hc
  · exact Or.inl (Or.inr ⟨he,hc⟩)
  · exact Or.inr (Or.inr ⟨he.symm,hc⟩)

/-- Specification of one merge. The operational module implements its
head comparison through actual integer-register branches. -/
def merge (left right : List SparseEntry) : List SparseEntry :=
  List.merge left right (fun a b => decide (KeyLE a b))

theorem merge_perm (left right : List SparseEntry) :
    (merge left right).Perm (left++right) := List.merge_perm_append _

theorem merge_length (left right : List SparseEntry) :
    (merge left right).length=left.length+right.length := by
  simpa using (merge_perm left right).length_eq

theorem merge_sorted (left right : List SparseEntry)
    (hl : left.Pairwise KeyLE) (hr : right.Pairwise KeyLE) :
    (merge left right).Pairwise KeyLE := by
  have ht (a b c : SparseEntry) :
      decide (KeyLE a b) → decide (KeyLE b c) → decide (KeyLE a c) := by
    simpa using keyLE_trans a b c
  have htot (a b : SparseEntry) : (decide (KeyLE a b) || decide (KeyLE b a)) = true := by
    simpa using keyLE_total a b
  simpa only [merge,decide_eq_true_eq] using List.pairwise_merge ht htot left right
    (by simpa using hl) (by simpa using hr)

end Maxwell.Cost.RealSparseOrder
