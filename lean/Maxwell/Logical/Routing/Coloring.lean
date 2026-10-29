import Maxwell.Logical.Routing.Doubling
import Maxwell.Logical.Routing
import Mathlib.Logic.Equiv.Fin.Basic

/-! Recursive incidence coloring by actual alternating-cycle bisection. -/

namespace Maxwell.Logical.Routing.Coloring

open Equiv

abbrev BinaryToken (Column Row : Type*) := (Bool × Column) × Row

/-- Pair the two incidences belonging to each source row and column pair. -/
def sourcePair (C R : Type*) : Perm (BinaryToken C R) where
  toFun p := ((!p.1.1, p.1.2), p.2)
  invFun p := ((!p.1.1, p.1.2), p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem sourcePair_involutive (C R : Type*) : Function.Involutive (sourcePair C R) := by
  intro p
  simp [sourcePair]

theorem sourcePair_no_fixed (C R : Type*) (p : BinaryToken C R) : sourcePair C R p ≠ p := by
  intro h
  have hh := congrArg (fun p : BinaryToken C R => p.1.1) h
  change (!p.1.1) = p.1.1 at hh
  cases hbit : p.1.1 <;> simp only [hbit, Bool.not_false, Bool.not_true] at hh <;> cases hh

/-- Source and target pairings whose common alternating cycles halve every row. -/
structure BinarySplit {C R : Type*} (target : Perm (BinaryToken C R)) where
  color : BinaryToken C R → Bool
  source_pair : ∀ p, color (sourcePair C R p) = !(color p)
  target_pair : ∀ p, color (target.symm (sourcePair C R p)) = !(color (target.symm p))

def binarySplit {C R : Type*} [Fintype C] [Fintype R] {size : ℕ}
    (index : BinaryToken C R ≃ Fin size) (target : Perm (BinaryToken C R)) : BinarySplit target := by
  classical
  letI : LinearOrder (BinaryToken C R) := LinearOrder.lift'
    index index.injective
  let a := sourcePair C R
  let b := target.symm * a * target
  have ha : Function.Involutive a := sourcePair_involutive C R
  have hb : Function.Involutive b := by
    intro p
    simp only [b, Perm.mul_apply, Equiv.apply_symm_apply, ha (target p)]
    exact target.symm_apply_apply p
  have hfa : ∀ p, a p ≠ p := sourcePair_no_fixed C R
  have hfb : ∀ p, b p ≠ p := by
    intro p he
    apply hfa (target p)
    have hh := congrArg target he
    simpa only [b, Perm.mul_apply, Equiv.apply_symm_apply] using hh
  let values := Doubling.colors index a b
  refine ⟨(fun p => values.get (index p)), ?_, ?_⟩
  · intro p
    simpa only [values, Doubling.colors_correct] using CycleColor.color_pair_a a b ha hb hfa hfb p
  · intro p
    have hh := CycleColor.color_pair_b a b ha hb hfa hfb (target.symm p)
    simpa only [values, Doubling.colors_correct, b, Perm.mul_apply, Equiv.apply_symm_apply] using hh

/-- The tail-column and row coordinates after removing one binary column bit. -/
def tail {C R : Type*} (p : BinaryToken C R) : C × R := (p.1.2, p.2)

/-- Each color selects exactly one incidence from every source pair. -/
def fiberEquiv {C R : Type*} (color : BinaryToken C R → Bool)
    (hflip : ∀ p, color (sourcePair C R p) = !(color p)) (bit : Bool) :
    {p : BinaryToken C R // color p = bit} ≃ C × R where
  toFun p := tail p.val
  invFun p :=
    if h : color ((false, p.1), p.2) = bit then ⟨((false, p.1), p.2), h⟩
    else ⟨((true, p.1), p.2), by
      have hh := hflip ((false, p.1), p.2)
      change color ((true, p.1), p.2) = !(color ((false, p.1), p.2)) at hh
      rw [hh]
      cases hc : color ((false, p.1), p.2) <;> cases bit <;> simp_all⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨side, c⟩, r⟩, hp⟩
    cases side
    · simp only [tail, hp, ↓reduceDIte]
    · have hh := hflip ((false, c), r)
      change color ((true, c), r) = !(color ((false, c), r)) at hh
      have hn : color ((false, c), r) ≠ bit := by
        intro he
        rw [hp, he] at hh
        cases bit <;> contradiction
      simp only [tail, hn, ↓reduceDIte]
  right_inv p := by
    dsimp only
    split_ifs <;> rfl

/-- Restrict the given target permutation to one actual split color. -/
def fiberTarget {C R : Type*} (target : Perm (BinaryToken C R))
    (color : BinaryToken C R → Bool) (bit : Bool) :
    {p : BinaryToken C R // color p = bit} ≃
      {p : BinaryToken C R // color (target.symm p) = bit} where
  toFun p := ⟨target p.val, by simpa only [Equiv.symm_apply_apply] using p.property⟩
  invFun p := ⟨target.symm p.val, p.property⟩
  left_inv p := by apply Subtype.ext; exact target.symm_apply_apply p.val
  right_inv p := by apply Subtype.ext; exact target.apply_symm_apply p.val

/-- The actual half-degree target permutation for one recursive color. -/
def reducedTarget {C R : Type*} (target : Perm (BinaryToken C R))
    (split : BinarySplit target) (bit : Bool) : Perm (C × R) :=
  ((fiberEquiv split.color split.source_pair bit).symm.trans (fiberTarget target split.color bit)).trans
    (fiberEquiv (fun p => split.color (target.symm p)) split.target_pair bit)

/-- Removing the chosen color bit commutes exactly with the target permutation. -/
theorem reducedTarget_tail {C R : Type*} (target : Perm (BinaryToken C R))
    (split : BinarySplit target) (p : BinaryToken C R) :
    reducedTarget target split (split.color p) (tail p) = tail (target p) := by
  have he := (fiberEquiv split.color split.source_pair (split.color p)).symm_apply_apply
    (⟨p, rfl⟩ : {p' // split.color p' = split.color p})
  change (fiberEquiv split.color split.source_pair (split.color p)).symm (tail p) = ⟨p, rfl⟩ at he
  simp only [reducedTarget, Equiv.trans_apply]
  rw [he]
  rfl

/-- Binary column labels, with the least-significant recursive bit explicit. -/
def Columns : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Columns n

instance columnsFintype : (n : ℕ) → Fintype (Columns n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := columnsFintype n
    exact inferInstanceAs (Fintype (Bool × Columns n))

/-- Explicit binary arithmetic indexing, with no choice of enumeration. -/
def columnsFinEquiv : (n : ℕ) → Columns n ≃ Fin (2 ^ n)
  | 0 => finOneEquiv.symm
  | n + 1 => ((finTwoEquiv.symm.prodCongr (columnsFinEquiv n)).trans
      finProdFinEquiv).trans (finCongr (pow_succ' 2 n).symm)

def columnRowIndex {R : Type*} {rows : ℕ} (n : ℕ) (rowIndex : R ≃ Fin rows) :
    Columns n × R ≃ Fin (2 ^ n * rows) :=
  ((columnsFinEquiv n).prodCongr rowIndex).trans finProdFinEquiv

/-- Store both directions once, making subsequent permutation queries array reads. -/
def storedPerm {α : Type*} {size : ℕ} (index : α ≃ Fin size) (target : Perm α) : Perm α :=
  let forward := Vector.ofFn (fun i => target (index.symm i))
  let backward := Vector.ofFn (fun i => target.symm (index.symm i))
  { toFun := fun p => forward.get (index p)
    invFun := fun p => backward.get (index p)
    left_inv := by intro p; simp [forward, backward, Vector.get, Fin.cast]
    right_inv := by intro p; simp [forward, backward, Vector.get, Fin.cast] }

@[simp] theorem storedPerm_eq {α : Type*} {size : ℕ} (index : α ≃ Fin size) (target : Perm α) :
    storedPerm index target = target := by
  ext p
  simp [storedPerm, Vector.get, Fin.cast]

/-- A proper incidence coloring, with arbitrary finite row and column types. -/
structure Proper {C R : Type*} (target : Perm (C × R)) where
  color : C × R → C
  source_unique : ∀ a b, a.2 = b.2 → color a = color b → a = b
  target_unique : ∀ a b, (target a).2 = (target b).2 → color a = color b → a = b

/-- Materialize every output label once, sharing all computed child arrays. -/
def storedProper {C R : Type*} {target : Perm (C × R)} {size : ℕ}
    (index : C × R ≃ Fin size) (proper : Proper target) : Proper target := by
  let values := Vector.ofFn (fun i => proper.color (index.symm i))
  have he (p : C × R) : values.get (index p) = proper.color p := by
    simp [values, Vector.get, Fin.cast]
  refine ⟨(fun p => values.get (index p)), ?_, ?_⟩
  · intro a b hrow hcolor
    exact proper.source_unique a b hrow (by simpa only [he] using hcolor)
  · intro a b hrow hcolor
    exact proper.target_unique a b hrow (by simpa only [he] using hcolor)

/-- Recursively bisect the actual incidence permutation. The cycle split
is constructed at each node, so proper coloring is a theorem, not an input. -/
def recursiveColoring {R : Type*} [Fintype R] {rows : ℕ} (rowIndex : R ≃ Fin rows) :
    (n : ℕ) → (target : Perm (Columns n × R)) → Proper target
  | 0, target => {
      color := fun _ => ()
      source_unique := by
        intro a b hrow _
        exact Prod.ext (Subsingleton.elim (α := Unit) _ _) hrow
      target_unique := by
        intro a b hrow _
        exact target.injective (Prod.ext (Subsingleton.elim (α := Unit) _ _) hrow) }
  | n + 1, target => by
      let index := columnRowIndex (n + 1) rowIndex
      let saved := storedPerm index target
      have hs : saved = target := storedPerm_eq index target
      suffices Proper saved from hs ▸ this
      refine storedProper index ?_
      let target := saved
      let split := binarySplit index target
      let left := recursiveColoring rowIndex n (reducedTarget target split false)
      let right := recursiveColoring rowIndex n (reducedTarget target split true)
      let small : (bit : Bool) → Proper (reducedTarget target split bit) := fun bit =>
        match bit with | false => left | true => right
      refine ⟨(fun p => (split.color p, (small (split.color p)).color (tail p))), ?_, ?_⟩
      · intro a b hrow hcolor
        have hbit : split.color a = split.color b := congrArg Prod.fst hcolor
        have hsmall : (small (split.color a)).color (tail a) = (small (split.color a)).color (tail b) := by
          have hc := congrArg Prod.snd hcolor
          change (small (split.color a)).color (tail a) = (small (split.color b)).color (tail b) at hc
          rw [← hbit] at hc
          exact hc
        have ht := (small (split.color a)).source_unique (tail a) (tail b) hrow hsmall
        have he := (fiberEquiv split.color split.source_pair (split.color a)).injective
          (a₁ := ⟨a, rfl⟩) (a₂ := ⟨b, hbit.symm⟩) ht
        exact congrArg Subtype.val he
      · intro a b hrow hcolor
        have hbit : split.color a = split.color b := congrArg Prod.fst hcolor
        have hsmall : (small (split.color a)).color (tail a) = (small (split.color a)).color (tail b) := by
          have hc := congrArg Prod.snd hcolor
          change (small (split.color a)).color (tail a) = (small (split.color b)).color (tail b) at hc
          rw [← hbit] at hc
          exact hc
        have hra := congrArg Prod.snd (reducedTarget_tail target split a)
        have hrb := congrArg Prod.snd (reducedTarget_tail target split b)
        rw [← hbit] at hrb
        have hr : (reducedTarget target split (split.color a) (tail a)).2 =
            (reducedTarget target split (split.color a) (tail b)).2 := hra.trans (hrow.trans hrb.symm)
        have ht := (small (split.color a)).target_unique (tail a) (tail b) hr hsmall
        have he := (fiberEquiv split.color split.source_pair (split.color a)).injective
          (a₁ := ⟨a, rfl⟩) (a₂ := ⟨b, hbit.symm⟩) ht
        exact congrArg Subtype.val he

theorem columns_card (n : ℕ) : Fintype.card (Columns n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Columns n) = _
    simp only [Fintype.card_prod, Fintype.card_bool, ih, pow_succ']

/-- Relabel columns while retaining the exact row incidence invariant. -/
def transportProper {C D R : Type*} (column : C ≃ D) (target : Perm (D × R))
    (proper : Proper (((column.prodCongr (Equiv.refl R)).trans target).trans
      (column.prodCongr (Equiv.refl R)).symm)) : Proper target := by
  let ports := column.prodCongr (Equiv.refl R)
  refine ⟨(fun p => column (proper.color (ports.symm p))), ?_, ?_⟩
  · intro a b hrow hcolor
    apply ports.symm.injective
    apply proper.source_unique
    · exact hrow
    · exact column.injective hcolor
  · intro a b hrow hcolor
    apply ports.symm.injective
    apply proper.target_unique
    · change (target (ports (ports.symm a))).2 = (target (ports (ports.symm b))).2
      simpa only [Equiv.apply_symm_apply] using hrow
    · exact column.injective hcolor

/-- Every square permutation of power-of-two side has a proper row coloring,
constructed by recursive alternating-cycle splits. -/
def rowColoring (n : ℕ) (target : Perm (Maxwell.Logical.Routing.Port (2 ^ n))) :
    Maxwell.Logical.Routing.RowColoring target := by
  let column := columnsFinEquiv n
  let ports := column.prodCongr (Equiv.refl (Fin (2 ^ n)))
  let proper := transportProper column target (recursiveColoring (Equiv.refl _) n ((ports.trans target).trans ports.symm))
  exact ⟨proper.color, proper.source_unique, proper.target_unique⟩

/-- The routing side chosen from the graph size is always supported by the
same executable coloring construction. -/
def portSideColoring (vertices : ℕ) (target : Perm (Port (portSide vertices))) :
    RowColoring target := by
  revert target
  rw [portSide_power_two]
  exact rowColoring (Nat.clog 4 vertices + 1)

end Maxwell.Logical.Routing.Coloring
