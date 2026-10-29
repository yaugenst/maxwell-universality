import Maxwell.Cost.DoublingInit.Encoding

/-! Logical views of partially written arrays; none are machine inputs. -/
namespace Maxwell.Cost.CalibrationMatrix.GenerationPrefix

/-- The prefix already overwritten by the initializer, retaining the actual
prior memory words only in the not-yet-visited suffix. -/
def written {n : ℕ} (initial expected : Vector (List Bool) n) (k : ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => if i.val < k then expected.get i else initial.get i

@[simp] theorem get_written {n : ℕ} (initial expected : Vector (List Bool) n) (k : ℕ) (i : Fin n) :
    (written initial expected k).get i = if i.val < k then expected.get i else initial.get i := by
  simp [written,Vector.get,Fin.cast]

theorem zero {n : ℕ} (initial expected : Vector (List Bool) n) : written initial expected 0 = initial := by
  apply Vector.ext
  intro i hi
  change (written initial expected 0).get ⟨i,hi⟩ = initial.get ⟨i,hi⟩
  simp

theorem complete {n : ℕ} (initial expected : Vector (List Bool) n) : written initial expected n = expected := by
  apply Vector.ext
  intro i hi
  change (written initial expected n).get ⟨i,hi⟩ = expected.get ⟨i,hi⟩
  simp [hi]

theorem step {n : ℕ} (initial expected : Vector (List Bool) n) (i : Fin n) :
    (written initial expected i.val).set i (expected.get i) = written initial expected (i.val+1) := by
  apply Vector.ext
  intro j hj
  change ((written initial expected i.val).set i (expected.get i)).get ⟨j,hj⟩ =
    (written initial expected (i.val+1)).get ⟨j,hj⟩
  simp only [Maxwell.Logical.Routing.DummyFill.get_set,get_written]
  by_cases hi : i.val = j
  · have hij : i = (⟨j,hj⟩ : Fin n) := Fin.ext hi
    simp [hij]
  · have hij : i ≠ (⟨j,hj⟩ : Fin n) := fun h => hi (congrArg Fin.val h)
    simp only [hij,ite_false]
    have hlt : ((⟨j,hj⟩ : Fin n).val < i.val) ↔ ((⟨j,hj⟩ : Fin n).val < i.val+1) := by
      change (j < i.val) ↔ (j < i.val+1)
      omega
    simp only [hlt]

theorem length {n : ℕ} (initial expected : Vector (List Bool) n) (width k : ℕ)
    (hi : ∀ i, (initial.get i).length = width) (he : ∀ i, (expected.get i).length = width) :
    ∀ i, ((written initial expected k).get i).length = width := by
  intro i
  rw [get_written]
  split_ifs <;> first | exact he i | exact hi i

end Maxwell.Cost.CalibrationMatrix.GenerationPrefix
