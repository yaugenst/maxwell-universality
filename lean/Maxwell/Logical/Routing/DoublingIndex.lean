import Maxwell.Logical.Routing.Doubling

/-! Flatten the saved permutation/minimum arrays into their arithmetic
indices. The source coloring already orders labels by these indices, so
every subsequent doubling pass uses only direct numeric array accesses. -/
namespace Maxwell.Logical.Routing.Doubling

/-- Numeric labels in exactly the same saved array slots. -/
def flatten {α : Type*} {n : ℕ} (index : α ≃ Fin n) (state : State α n) : State (Fin n) n :=
  ⟨state.jump.map index, state.minimum.map index⟩

theorem flatten_initial {α : Type*} {n : ℕ} (index : α ≃ Fin n) (p : Equiv.Perm α) :
    flatten index (initial index p) =
      initial (Equiv.refl (Fin n)) (index.permCongr p) := by
  simp only [flatten, initial, Vector.map_ofFn]
  congr 1
  congr 1
  funext i
  exact index.apply_symm_apply i

theorem flatten_step {α : Type*} {n : ℕ} (index : α ≃ Fin n) (state : State α n) :
    letI : LinearOrder α := LinearOrder.lift' index index.injective
    flatten index (step index state) = step (Equiv.refl (Fin n)) (flatten index state) := by
  let : LinearOrder α := LinearOrder.lift' index index.injective
  have hmin (x y : α) : index (min x y) = min (index x) (index y) := by
    by_cases h : index x ≤ index y
    · rw [min_eq_left (show x ≤ y from h), min_eq_left h]
    · rw [min_eq_right (show y ≤ x from le_of_not_ge h), min_eq_right (le_of_not_ge h)]
  simp only [flatten, step, Vector.map_ofFn]
  congr 1
  · apply Vector.ext
    intro i hi
    simp [jumpAt, Vector.get, Fin.cast]
  · apply Vector.ext
    intro i hi
    simp [minAt, Vector.get, Fin.cast, hmin]

theorem flatten_run {α : Type*} {n : ℕ} (index : α ≃ Fin n) (p : Equiv.Perm α) (rounds : ℕ) :
    letI : LinearOrder α := LinearOrder.lift' index index.injective
    flatten index (run index p rounds) =
      run (Equiv.refl (Fin n)) (index.permCongr p) rounds := by
  let : LinearOrder α := LinearOrder.lift' index index.injective
  induction rounds with
  | zero => exact flatten_initial index p
  | succ rounds ih =>
    change flatten index (step index (run index p rounds)) = _
    rw [flatten_step, ih]
    rfl

end Maxwell.Logical.Routing.Doubling
