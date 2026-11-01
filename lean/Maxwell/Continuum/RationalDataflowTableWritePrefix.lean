import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! A forward table writer extends an exact prefix one entry at a time.
The invariant is independent of the function producing each value. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost

def Table.CorrectPrefix {n : ℕ} (a : Table n) (values : ℕ→Parts) (count : ℕ) : Prop :=
  ∀j:Fin n,j.val<count→a.get j=values j.val

theorem Table.CorrectPrefix.empty {n : ℕ} (a : Table n) (values : ℕ→Parts) :
    a.CorrectPrefix values 0 := by intro j hj;omega

theorem Table.CorrectPrefix.next {n : ℕ} {a : Table n} {values : ℕ→Parts} (i : Fin n)
    (h : a.CorrectPrefix values i.val) (hw : (values i.val).Width (addressValue a.width)) :
    (a.set i (values i.val)).CorrectPrefix values (i.val+1) := by
  intro j hj
  by_cases he : i=j
  · subst j
    exact a.set_get i (values i.val) hw
  · rw [a.set_get_ne i j (values i.val) he]
    apply h j
    have hne : i.val ≠ j.val := fun heq=>he (Fin.ext heq)
    omega


theorem Table.CorrectPrefix.congr {n count : ℕ} {a : Table n} {values other : ℕ→Parts}
    (h : a.CorrectPrefix values count) (same : ∀k,k<count→values k=other k) :
    a.CorrectPrefix other count := fun k hk=>(h k hk).trans (same k.val hk)

#print axioms Table.CorrectPrefix.next
end Maxwell.Continuum.RationalDataflow.PartArray
