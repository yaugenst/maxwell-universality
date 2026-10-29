import Maxwell.Cost.BinarySplit.Pipeline

namespace Maxwell.Cost.BinarySplit
open Maxwell.Logical.Routing
open Coloring.NumericSplit

private theorem indexed_conjugate {α : Type*} {n : ℕ} (index : α ≃ Fin n) (a b : Equiv.Perm α) :
    Doubling.indexedColors (Equiv.refl (Fin n)) (index.permCongr a) (index.permCongr b) =
      Doubling.indexedColors index a b := by
  have hm : index.permCongr a * index.permCongr b = index.permCongr (a*b) := by
    ext i
    simp [Equiv.permCongr_apply]
  have hr (p : Equiv.Perm (Fin n)) : (Equiv.refl (Fin n)).permCongr p=p := rfl
  simp only [Doubling.indexedColors,hm,hr]

/-- The emitted numeric colors are exactly the colors used by the existing
recursive routing algorithm, with the same deterministic order on labels. -/
theorem colors_eq_binarySplit {C R : Type*} [Fintype C] [Fintype R]
    (k : ℕ) (index : C × R ≃ Fin (2^k)) (target : Equiv.Perm (Coloring.BinaryToken C R)) :
    colors k (numericPerm (halfIndex index) target) =
      Vector.ofFn (fun i => (Coloring.binarySplit (halfIndex index) target).color ((halfIndex index).symm i)) := by
  have ha : (halfIndex index).permCongr (Coloring.sourcePair C R)=halfSwap (2^k) :=
    numeric_sourcePair index
  have hb : (halfIndex index).permCongr (target.symm*Coloring.sourcePair C R*target)=
      (numericPerm (halfIndex index) target).symm*halfSwap (2^k)*numericPerm (halfIndex index) target := by
    apply Equiv.ext
    intro i
    exact numeric_targetPair index target i
  rw [colors,← hb,← ha,indexed_conjugate]
  have he := Doubling.colors_eq_indexed (halfIndex index) (Coloring.sourcePair C R)
    (target.symm*Coloring.sourcePair C R*target)
  rw [← he]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn,Coloring.binarySplit,Equiv.apply_symm_apply]
  rfl

end Maxwell.Cost.BinarySplit
