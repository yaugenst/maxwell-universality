import Maxwell.Certificate.Coverage

namespace Maxwell.Certificate.FrozenCover

/-- The Gamma-region upper bound. Nonnegativity comes from the root box. -/
def Gamma (x : Fin 3 → ℝ) : Prop := ∀ i, x i ≤ 1/8

def gammaCheck (b : Box) : Bool := decide (∀ i, b.hi i ≤ 1/8)

theorem gammaCheck_sound {b : Box} (h : gammaCheck b = true)
    {x : Fin 3 → ℝ} (hx : b.Contains x) : Gamma x := by
  have hq : ∀ i, b.hi i ≤ 1/8 := of_decide_eq_true h
  intro i
  have hr : (b.hi i : ℝ) ≤ 1/8 := by
    have hc : (b.hi i : ℝ) ≤ ((1/8 : ℚ) : ℝ) := Rat.cast_le.mpr (hq i)
    norm_num at hc ⊢
    exact hc
  exact (hx i).2.trans hr

/-- The three accepted alternatives for a real point in the ordered wedge. -/
def Region {n : Nat} (matrixBoxes : Fin n → Box) (x : Fin 3 → ℝ) : Prop :=
  Gamma x ∨ Box.LocalBall x ∨ ∃ i, (matrixBoxes i).Contains x

/-- Tags 0, 1, and 2 denote empty-wedge, Gamma, and local-ball leaves.
Every remaining tag must identify its exact box in the finite matrix list. -/
def leafCheck {n : Nat} (matrixBoxes : Fin n → Box) (tag : Nat) (b : Box) : Bool :=
  if tag = 0 then b.emptyWedgeCheck
  else if tag = 1 then gammaCheck b
  else if tag = 2 then b.localBallCheck
  else if h : tag - 3 < n then decide (∀ j,
    b.lo j = (matrixBoxes ⟨tag - 3, h⟩).lo j ∧
    b.hi j = (matrixBoxes ⟨tag - 3, h⟩).hi j)
  else false

theorem leafCheck_sound {n : Nat} (matrixBoxes : Fin n → Box) (tag : Nat) (b : Box)
    (h : leafCheck matrixBoxes tag b = true) (x : Fin 3 → ℝ)
    (hx : b.Contains x) (hw : Box.Wedge x) : Region matrixBoxes x := by
  unfold leafCheck at h
  split at h
  · exact False.elim (Box.emptyWedgeCheck_sound h hx hw)
  · split at h
    · exact Or.inl (gammaCheck_sound h hx)
    · split at h
      · exact Or.inr (Or.inl (Box.localBallCheck_sound h hx))
      · split at h
        next hbound =>
          have he : ∀ j, b.lo j = (matrixBoxes ⟨tag - 3, hbound⟩).lo j ∧
              b.hi j = (matrixBoxes ⟨tag - 3, hbound⟩).hi j := of_decide_eq_true h
          have hlo : b.lo = (matrixBoxes ⟨tag - 3, hbound⟩).lo := funext fun j => (he j).1
          have hhi : b.hi = (matrixBoxes ⟨tag - 3, hbound⟩).hi := funext fun j => (he j).2
          have hb : b = matrixBoxes ⟨tag - 3, hbound⟩ := by
            exact congrArg₂ Box.mk hlo hhi
          exact Or.inr (Or.inr ⟨⟨tag - 3, hbound⟩, hb ▸ hx⟩)
        next => contradiction

/-- A successful tagged tree covers every real point of the root box lying
in the ordered wedge, including all shared closed faces. -/
theorem check_sound {n : Nat} (matrixBoxes : Fin n → Box)
    (tree : CoverTree) (b : Box) (h : tree.check (leafCheck matrixBoxes) b = true)
    (x : Fin 3 → ℝ) (hx : b.Contains x) (hw : Box.Wedge x) :
    Region matrixBoxes x := by
  exact CoverTree.check_sound (leafCheck matrixBoxes)
    (fun x => Box.Wedge x → Region matrixBoxes x)
    (leafCheck_sound matrixBoxes) tree b h x hx hw

end Maxwell.Certificate.FrozenCover
