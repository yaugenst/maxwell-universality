import Maxwell.Logical.Routing.DoublingIndex

/-! The final alternating-cycle colors are comparisons of numeric minimum
array entries, after the materialized index-only doubling passes. -/
namespace Maxwell.Logical.Routing.Doubling

@[simp] theorem minAt_flatten {α : Type*} {n : ℕ} (index : α ≃ Fin n)
    (state : State α n) (x : α) :
    minAt (Equiv.refl (Fin n)) (flatten index state) (index x) = index (minAt index state x) := by
  simp [flatten, minAt, Vector.get, Fin.cast]

@[simp] theorem jumpAt_flatten {α : Type*} {n : ℕ} (index : α ≃ Fin n)
    (state : State α n) (x : α) :
    jumpAt (Equiv.refl (Fin n)) (flatten index state) (index x) = index (jumpAt index state x) := by
  simp [flatten, jumpAt, Vector.get, Fin.cast]

/-- One numeric array comparison pass after a shared numeric doubling run. -/
def indexedColors {α : Type*} {n : ℕ} (index : α ≃ Fin n) (a b : Equiv.Perm α) : Vector Bool n :=
  let saved := run (Equiv.refl (Fin n)) (index.permCongr (a * b)) (Nat.clog 2 n)
  Vector.ofFn (fun i => decide (minAt (Equiv.refl (Fin n)) saved i <
    minAt (Equiv.refl (Fin n)) saved ((index.permCongr a) i)))

theorem colors_eq_indexed {α : Type*} {n : ℕ} (index : α ≃ Fin n) (a b : Equiv.Perm α) :
    letI : LinearOrder α := LinearOrder.lift' index index.injective
    colors index a b = indexedColors index a b := by
  let : LinearOrder α := LinearOrder.lift' index index.injective
  have hm (x : α) : index (minAt index (run index (a * b) (Nat.clog 2 n)) x) =
      minAt (Equiv.refl (Fin n))
        (run (Equiv.refl (Fin n)) (index.permCongr (a * b)) (Nat.clog 2 n)) (index x) := by
    rw [← flatten_run index (a * b), minAt_flatten]
  apply Vector.ext
  intro i hi
  simp only [colors, indexedColors, Vector.getElem_ofFn]
  change decide (index (minAt index (run index (a * b) (Nat.clog 2 n)) (index.symm ⟨i, hi⟩)) <
    index (minAt index (run index (a * b) (Nat.clog 2 n)) (a (index.symm ⟨i, hi⟩)))) = _
  rw [hm, hm, index.apply_symm_apply]
  rfl

end Maxwell.Logical.Routing.Doubling
