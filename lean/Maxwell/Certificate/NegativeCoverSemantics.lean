import Maxwell.Certificate.Coverage

namespace Maxwell.Certificate.FrozenNegativeCover

/-- The larger Gamma cube used by the original material's negative trials. -/
def Gamma (x : Fin 3 → ℝ) : Prop := ∀ i, x i ≤ 3/16

def gammaCheck (b : Box) : Bool := decide (∀ i, b.hi i ≤ 3/16)

theorem gammaCheck_sound {b : Box} (h : gammaCheck b = true)
    {x : Fin 3 → ℝ} (hx : b.Contains x) : Gamma x := by
  have hq : ∀ i, b.hi i ≤ 3/16 := of_decide_eq_true h
  intro i
  have hr : (b.hi i : ℝ) ≤ 3/16 := by
    have hc : (b.hi i : ℝ) ≤ ((3/16 : ℚ) : ℝ) := Rat.cast_le.mpr (hq i)
    norm_num at hc ⊢
    exact hc
  exact (hx i).2.trans hr

def Region {n : Nat} (matrixBoxes : Fin n → Box) (x : Fin 3 → ℝ) : Prop :=
  Gamma x ∨ ∃ i, (matrixBoxes i).Contains x

/-- Tags zero and one mark empty-wedge and Gamma leaves. All other tags
must name the inherited rational box exactly. -/
def leafCheck {n : Nat} (matrixBoxes : Fin n → Box) (tag : Nat) (b : Box) : Bool :=
  if tag = 0 then b.emptyWedgeCheck
  else if tag = 1 then gammaCheck b
  else if h : tag - 2 < n then decide (∀ j,
    b.lo j = (matrixBoxes ⟨tag - 2, h⟩).lo j ∧
    b.hi j = (matrixBoxes ⟨tag - 2, h⟩).hi j)
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
      next hbound =>
        have he : ∀ j, b.lo j = (matrixBoxes ⟨tag - 2, hbound⟩).lo j ∧
            b.hi j = (matrixBoxes ⟨tag - 2, hbound⟩).hi j := of_decide_eq_true h
        have hlo : b.lo = (matrixBoxes ⟨tag - 2, hbound⟩).lo := funext fun j => (he j).1
        have hhi : b.hi = (matrixBoxes ⟨tag - 2, hbound⟩).hi := funext fun j => (he j).2
        have hb : b = matrixBoxes ⟨tag - 2, hbound⟩ := congrArg₂ Box.mk hlo hhi
        exact Or.inr ⟨⟨tag - 2, hbound⟩, hb ▸ hx⟩
      next => contradiction

theorem check_sound {n : Nat} (matrixBoxes : Fin n → Box)
    (tree : CoverTree) (b : Box) (h : tree.check (leafCheck matrixBoxes) b = true)
    (x : Fin 3 → ℝ) (hx : b.Contains x) (hw : Box.Wedge x) :
    Region matrixBoxes x :=
  CoverTree.check_sound (leafCheck matrixBoxes)
    (fun x => Box.Wedge x → Region matrixBoxes x)
    (leafCheck_sound matrixBoxes) tree b h x hx hw

end Maxwell.Certificate.FrozenNegativeCover
