import Maxwell.Continuum.RationalDataflowSequence

/-! Fixed arithmetic fragments preserve unused logical registers and can
execute in the larger bank of an enclosing fixed program. -/

namespace Maxwell.Continuum.RationalDataflow

theorem Instruction.Valid.mono {a : Instruction} {S T : Finset ℕ}
    (h : a.Valid S) (hST : S ⊆ T) : a.Valid T := by
  cases a with
  | literal target q => exact hST h
  | binary op target left right => exact ⟨hST h.1,hST h.2.1,hST h.2.2⟩
  | inverse target source => exact ⟨hST h.1,hST h.2⟩

theorem Control.Valid.mono {c : Control} {S T : Finset ℕ}
    (h : c.Valid S) (hST : S ⊆ T) : c.Valid T := by
  induction c with
  | done => trivial
  | step a rest ih => exact ⟨h.1.mono hST,ih h.2⟩
  | positive source yes no iy ino => exact ⟨hST h.1,iy h.2.1,ino h.2.2⟩

theorem Instruction.update_outside (a : Instruction) (S : Finset ℕ) (ha : a.Valid S)
    (v : ℕ → Parts) (i : ℕ) (hi : i ∉ S) : a.update v i=v i := by
  cases a with
  | literal target q =>
    exact Function.update_of_ne (show i≠target from fun h => hi (h.symm ▸ ha)) _ _
  | binary op target left right =>
    exact Function.update_of_ne (show i≠target from fun h => hi (h.symm ▸ ha.1)) _ _
  | inverse target source =>
    exact Function.update_of_ne (show i≠target from fun h => hi (h.symm ▸ ha.1)) _ _

theorem Control.evaluate_outside (c : Control) (S : Finset ℕ) (hc : c.Valid S)
    (v : ℕ → Parts) (i : ℕ) (hi : i ∉ S) : c.evaluate v i=v i := by
  induction c generalizing v with
  | done => rfl
  | step a rest ih => exact (ih hc.2 (a.update v)).trans (a.update_outside S hc.1 v i hi)
  | positive source yes no iy ino =>
    simp only [Control.evaluate]
    split_ifs
    · exact iy hc.2.1 v
    · exact ino hc.2.2 v

#print axioms Control.evaluate_outside

end Maxwell.Continuum.RationalDataflow
