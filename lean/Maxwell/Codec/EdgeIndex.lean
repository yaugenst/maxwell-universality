import Maxwell.Codec.Target

/-! Dense retained-edge addresses follow the target's orientation-major,
lexicographic order. Address arithmetic uses three dimensions and constants. -/
namespace Maxwell.Codec

abbrev tripleEquiv (a b c : ℕ) : (Fin a × Fin b × Fin c) ≃ Fin (a*(b*c)) :=
  (Equiv.prodCongr (Equiv.refl (Fin a)) finProdFinEquiv).trans finProdFinEquiv

@[simp] theorem tripleEquiv_val (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (tripleEquiv a b c (i,j,k)).val = (i.val*b+j.val)*c+k.val := by
  change (k.val+c*j.val)+(b*c)*i.val = _
  ring

def edgeCount (B : Target.Box) : ℕ :=
  B.nx*((B.ny-1)*(B.nz-1)) +
    ((B.nx-1)*(B.ny*(B.nz-1)) + (B.nx-1)*((B.ny-1)*B.nz))

abbrev edgeEquiv (B : Target.Box) : B.Edge ≃ Fin (edgeCount B) :=
  (Equiv.sumCongr (tripleEquiv B.nx (B.ny-1) (B.nz-1))
    ((Equiv.sumCongr (tripleEquiv (B.nx-1) B.ny (B.nz-1))
      (tripleEquiv (B.nx-1) (B.ny-1) B.nz)).trans finSumFinEquiv)).trans finSumFinEquiv

def edgeIndex {B : Target.Box} (e : B.Edge) : ℕ := (edgeEquiv B e).val

theorem edgeIndex_lt {B : Target.Box} (e : B.Edge) : edgeIndex e < edgeCount B :=
  (edgeEquiv B e).isLt

theorem edgeIndex_injective (B : Target.Box) : Function.Injective (@edgeIndex B) :=
  fun _ _ h => (edgeEquiv B).injective (Fin.ext h)

@[simp] theorem edgeIndex_x {B : Target.Box}
    (i : Fin B.nx) (j : Fin (B.ny-1)) (k : Fin (B.nz-1)) :
    edgeIndex (B := B) (.inl (i,j,k)) = (i.val*(B.ny-1)+j.val)*(B.nz-1)+k.val := by
  change (tripleEquiv B.nx (B.ny-1) (B.nz-1) (i,j,k)).val = _
  exact tripleEquiv_val _ _ _ _ _ _

@[simp] theorem edgeIndex_y {B : Target.Box}
    (i : Fin (B.nx-1)) (j : Fin B.ny) (k : Fin (B.nz-1)) :
    edgeIndex (B := B) (.inr (.inl (i,j,k))) =
      B.nx*((B.ny-1)*(B.nz-1))+(i.val*B.ny+j.val)*(B.nz-1)+k.val := by
  change B.nx*((B.ny-1)*(B.nz-1)) +
    (tripleEquiv (B.nx-1) B.ny (B.nz-1) (i,j,k)).val = _
  rw [tripleEquiv_val]
  omega

@[simp] theorem edgeIndex_z {B : Target.Box}
    (i : Fin (B.nx-1)) (j : Fin (B.ny-1)) (k : Fin B.nz) :
    edgeIndex (B := B) (.inr (.inr (i,j,k))) =
      B.nx*((B.ny-1)*(B.nz-1))+(B.nx-1)*(B.ny*(B.nz-1))+
        (i.val*(B.ny-1)+j.val)*B.nz+k.val := by
  change B.nx*((B.ny-1)*(B.nz-1)) + ((B.nx-1)*(B.ny*(B.nz-1))+
    (tripleEquiv (B.nx-1) (B.ny-1) B.nz (i,j,k)).val) = _
  rw [tripleEquiv_val]
  omega

theorem edgeCount_card (B : Target.Box) : edgeCount B = Fintype.card B.Edge := by
  exact (Fintype.card_congr (edgeEquiv B)).trans (Fintype.card_fin _) |>.symm

end Maxwell.Codec
