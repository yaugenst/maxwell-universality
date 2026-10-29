import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationMatrix

/-- The first `k` output slots have been replaced by their computed payloads. -/
def fillPrefix {n : ℕ} (initial : Vector (List Bool) n) (value : Fin n → List Bool)
    (k : ℕ) : Vector (List Bool) n := Vector.ofFn fun i => if i.val < k then value i else initial.get i

@[simp] theorem fillPrefix_zero {n : ℕ} (initial : Vector (List Bool) n) (value : Fin n → List Bool) :
    fillPrefix initial value 0 = initial := by
  apply Vector.ext
  intro i hi
  simp [fillPrefix, Vector.get]

@[simp] theorem fillPrefix_full {n : ℕ} (initial : Vector (List Bool) n) (value : Fin n → List Bool) :
    fillPrefix initial value n = Vector.ofFn value := by
  apply Vector.ext
  intro i hi
  simp [fillPrefix]

theorem fillPrefix_step {n : ℕ} (initial : Vector (List Bool) n) (value : Fin n → List Bool)
    (k : Fin n) : (fillPrefix initial value k.val).set k (value k) = fillPrefix initial value (k.val+1) := by
  apply Vector.ext
  intro i hi
  by_cases he : i = k.val
  · subst i
    simp [fillPrefix]
  · have hh : i < k.val+1 ↔ i < k.val := by omega
    simp only [Vector.getElem_set, ite_eq_right (Ne.symm he), fillPrefix, Vector.getElem_ofFn]
    change (if i < k.val then _ else _) = (if i < k.val+1 then _ else _)
    simp only [hh]

end Maxwell.Cost.CalibrationMatrix
