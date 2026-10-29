import Maxwell.Logical.Routing.Coloring

/-! Arithmetic coordinates for the actual recursive split.  The source pairing
is a half-array toggle; each child is obtained by one color test, one target
lookup, and reduction modulo the child length. -/
namespace Maxwell.Logical.Routing.Coloring.NumericSplit
open Equiv

variable {C R : Type*} {M : ℕ}

def halfIndex (index : C × R ≃ Fin M) : BinaryToken C R ≃ Fin (2*M) :=
  ((Equiv.prodAssoc Bool C R).trans (finTwoEquiv.symm.prodCongr index)).trans finProdFinEquiv

theorem halfIndex_val (index : C × R ≃ Fin M) (p : BinaryToken C R) :
    (halfIndex index p).val = (index (tail p)).val + M * (finTwoEquiv.symm p.1.1).val := rfl

@[simp] theorem halfIndex_false (index : C × R ≃ Fin M) (p : C × R) :
    (halfIndex index ((false,p.1),p.2)).val = (index p).val := by
  simp [halfIndex,finTwoEquiv,finProdFinEquiv]

@[simp] theorem halfIndex_true (index : C × R ≃ Fin M) (p : C × R) :
    (halfIndex index ((true,p.1),p.2)).val = (index p).val + M := by
  simp [halfIndex,finTwoEquiv,finProdFinEquiv]

/-- Actual numeric half-array toggle, including the empty array. -/
def halfStep (M : ℕ) (i : Fin (2*M)) : Fin (2*M) :=
  ⟨if i.val < M then i.val+M else i.val-M, by split_ifs <;> omega⟩

theorem halfStep_involutive (M : ℕ) : Function.Involutive (halfStep M) := by
  intro i
  apply Fin.ext
  change (if (if i.val < M then i.val+M else i.val-M) < M
    then (if i.val < M then i.val+M else i.val-M)+M
    else (if i.val < M then i.val+M else i.val-M)-M) = i.val
  split_ifs <;> omega

def halfSwap (M : ℕ) : Perm (Fin (2*M)) where
  toFun := halfStep M
  invFun := halfStep M
  left_inv := halfStep_involutive M
  right_inv := halfStep_involutive M

@[simp] theorem halfSwap_val (i : Fin (2*M)) :
    (halfSwap M i).val = if i.val < M then i.val+M else i.val-M := rfl

def numericPerm {α : Type*} {N : ℕ} (index : α ≃ Fin N) (p : Perm α) : Perm (Fin N) :=
  (index.symm.trans p).trans index

@[simp] theorem numericPerm_eq_permCongr {α : Type*} {N : ℕ} (index : α ≃ Fin N)
    (p : Perm α) : numericPerm index p = index.permCongr p := rfl

@[simp] theorem numericPerm_apply {α : Type*} {N : ℕ} (index : α ≃ Fin N)
    (p : Perm α) (i : Fin N) : numericPerm index p i = index (p (index.symm i)) := rfl

@[simp] theorem numericPerm_symm_apply {α : Type*} {N : ℕ} (index : α ≃ Fin N)
    (p : Perm α) (i : Fin N) : (numericPerm index p).symm i = index (p.symm (index.symm i)) := rfl

theorem halfIndex_sourcePair (index : C × R ≃ Fin M) (p : BinaryToken C R) :
    halfIndex index (sourcePair C R p) = halfSwap M (halfIndex index p) := by
  rcases p with ⟨⟨b,c⟩,r⟩
  change halfIndex index ((!b,c),r) = halfSwap M (halfIndex index ((b,c),r))
  apply Fin.ext
  rw [halfSwap_val,halfIndex_val,halfIndex_val]
  cases b <;> simp [tail,finTwoEquiv,(index (c,r)).isLt]

@[simp] theorem numeric_sourcePair (index : C × R ≃ Fin M) :
    numericPerm (halfIndex index) (sourcePair C R) = halfSwap M := by
  ext i
  simp only [numericPerm_apply,halfIndex_sourcePair,Equiv.apply_symm_apply]

/-- The target pairing is exactly two saved permutation lookups around the
same numeric source toggle. -/
theorem numeric_targetPair (index : C × R ≃ Fin M)
    (target : Perm (BinaryToken C R)) (i : Fin (2*M)) :
    numericPerm (halfIndex index) (target.symm * sourcePair C R * target) i =
      (numericPerm (halfIndex index) target).symm
        (halfSwap M (numericPerm (halfIndex index) target i)) := by
  simp only [numericPerm_apply,numericPerm_symm_apply,Perm.mul_apply]
  rw [← halfIndex_sourcePair,Equiv.symm_apply_apply]

def lower (i : Fin M) : Fin (2*M) := ⟨i.val,by omega⟩
def upper (i : Fin M) : Fin (2*M) := ⟨i.val+M,by omega⟩

theorem halfIndex_lower (index : C × R ≃ Fin M) (i : Fin M) :
    halfIndex index ((false,(index.symm i).1),(index.symm i).2) = lower i := by
  apply Fin.ext
  simp [lower]

theorem halfIndex_upper (index : C × R ≃ Fin M) (i : Fin M) :
    halfIndex index ((true,(index.symm i).1),(index.symm i).2) = upper i := by
  apply Fin.ext
  simp [upper]

/-- Choose the stored occurrence of the requested color in one source pair. -/
def selected (colors : Fin (2*M) → Bool) (bit : Bool) (i : Fin M) : Fin (2*M) :=
  if colors (lower i) = bit then lower i else upper i

theorem selected_eq_fiber (index : C × R ≃ Fin M)
    (color : BinaryToken C R → Bool)
    (hflip : ∀ p, color (sourcePair C R p) = !(color p)) (bit : Bool) (i : Fin M) :
    selected (fun j => color ((halfIndex index).symm j)) bit i =
      halfIndex index ((fiberEquiv color hflip bit).symm (index.symm i)).val := by
  have hl := halfIndex_lower index i
  have hu := halfIndex_upper index i
  have hs : (halfIndex index).symm (lower i) =
      ((false,(index.symm i).1),(index.symm i).2) := (Equiv.symm_apply_eq _).mpr hl.symm
  simp only [selected,hs,fiberEquiv,Equiv.coe_fn_symm_mk]
  split_ifs <;> first | exact hl.symm | exact hu.symm

theorem halfIndex_tail_mod (index : C × R ≃ Fin M) (p : BinaryToken C R) :
    (index (tail p)).val = (halfIndex index p).val % M := by
  rw [halfIndex_val,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (index (tail p)).isLt).symm

/-- A child target entry is the stored parent target at its selected source
occurrence, reduced modulo the child length. -/
theorem reducedTarget_val (index : C × R ≃ Fin M)
    (target : Perm (BinaryToken C R)) (split : BinarySplit target)
    (bit : Bool) (i : Fin M) :
    (numericPerm index (reducedTarget target split bit) i).val =
      (numericPerm (halfIndex index) target
        (selected (fun j => split.color ((halfIndex index).symm j)) bit i)).val % M := by
  rw [selected_eq_fiber]
  simp only [numericPerm_apply,Equiv.symm_apply_apply]
  change (index (tail (target ((fiberEquiv split.color split.source_pair bit).symm
    (index.symm i)).val))).val = _
  exact halfIndex_tail_mod index _

/-- The explicit binary column enumeration uses precisely these half-array
coordinates, up to the arithmetic equality of the two lengths. -/
theorem columnRowIndex_succ (n : ℕ) {rows : ℕ} (rowIndex : R ≃ Fin rows)
    (p : BinaryToken (Columns n) R) :
    (columnRowIndex (n+1) rowIndex p).val =
      (halfIndex (columnRowIndex n rowIndex) p).val := by
  rcases p with ⟨⟨b,c⟩,r⟩
  change (rowIndex r).val + rows * ((columnsFinEquiv n c).val +
      2^n * (finTwoEquiv.symm b).val) =
    (rowIndex r).val + rows * (columnsFinEquiv n c).val +
      (2^n * rows) * (finTwoEquiv.symm b).val
  ring

theorem columnRowIndex_succ_eq (n : ℕ) {rows : ℕ} (rowIndex : R ≃ Fin rows) :
    columnRowIndex (n+1) rowIndex =
      (halfIndex (columnRowIndex n rowIndex)).trans
        (finCongr (by rw [pow_succ']; exact (Nat.mul_assoc 2 (2^n) rows).symm)) := by
  ext p
  exact columnRowIndex_succ n rowIndex p

@[simp] theorem selected_val (colors : Fin (2*M) → Bool) (bit : Bool) (i : Fin M) :
    (selected colors bit i).val = if colors (lower i) = bit then i.val else i.val+M := by
  unfold selected
  split_ifs <;> rfl

/-- The same child formula directly consumes numeric array functions. -/
theorem reducedTarget_array (index : C × R ≃ Fin M)
    (target : Perm (BinaryToken C R)) (split : BinarySplit target)
    (colors : Fin (2*M) → Bool) (forward : Fin (2*M) → Fin (2*M))
    (hcolors : ∀ j, colors j = split.color ((halfIndex index).symm j))
    (hforward : ∀ j, forward j = numericPerm (halfIndex index) target j)
    (bit : Bool) (i : Fin M) :
    (numericPerm index (reducedTarget target split bit) i).val =
      (forward (selected colors bit i)).val % M := by
  rw [hforward]
  have hc : colors = fun j => split.color ((halfIndex index).symm j) := funext hcolors
  rw [hc]
  exact reducedTarget_val index target split bit i

end Maxwell.Logical.Routing.Coloring.NumericSplit
