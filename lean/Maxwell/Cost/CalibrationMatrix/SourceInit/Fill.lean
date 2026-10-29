import Maxwell.Cost.CalibrationMatrix.SourceInit.Write
import Maxwell.Cost.CalibrationMatrix.Fill

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

def zeroWords {m n : ℕ} (d : Data m n) (initial : Fin 4 → Vector (List Bool) n)
    (k : ℕ) : Fin 4 → Vector (List Bool) n :=
  fun port => fillPrefix (initial port) (fun _ => FixedWidth.bits (addressValue d.width) (0 : ℕ).bits) k

def outputWords {m n : ℕ} (d : Data m n) (k : ℕ) : Fin 4 → Vector (List Bool) n :=
  fun port => Vector.ofFn fun i => FixedWidth.bits (addressValue d.width)
    (if port = 0 ∨ port = 2 then (values d.records k).positive i
     else (values d.records k).negative i).bits

@[simp] theorem zeroWords_zero {m n : ℕ} (d : Data m n)
    (initial : Fin 4 → Vector (List Bool) n) : zeroWords d initial 0 = initial := by
  funext port
  simp [zeroWords]

theorem zeroWords_full {m n : ℕ} (d : Data m n)
    (initial : Fin 4 → Vector (List Bool) n) : zeroWords d initial n = outputWords d 0 := by
  funext port
  simp [zeroWords, outputWords]

theorem writtenWords_port {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (row : Fin n) (positive negative : ℕ) (port : Fin 4) :
    writtenWords d words row positive negative port = (words port).set row
      (FixedWidth.bits (addressValue d.width) (if port = 0 ∨ port = 2 then positive else negative).bits) := by
  fin_cases port <;> simp [writtenWords, setPair]

theorem zeroWords_step {m n : ℕ} (d : Data m n)
    (initial : Fin 4 → Vector (List Bool) n) (row : Fin n) :
    writtenWords d (zeroWords d initial row.val) row 0 0 = zeroWords d initial (row.val+1) := by
  funext port
  rw [writtenWords_port]
  simp only [ite_self, zeroWords]
  exact fillPrefix_step _ _ row

theorem outputWords_step {m n : ℕ} (d : Data m n) (j : Fin m) :
    writtenWords d (outputWords d j.val) (d.records.index j)
      ((values d.records j.val).positive (d.records.index j)+d.records.positive j)
      ((values d.records j.val).negative (d.records.index j)+d.records.negative j) =
      outputWords d (j.val+1) := by
  funext port
  rw [writtenWords_port]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, outputWords, Vector.getElem_ofFn,
    values_step_positive, values_step_negative]
  by_cases he : d.records.index j = ⟨i, hi⟩
  · simp [he]
  · have hv : (d.records.index j).val ≠ i := fun h => he (Fin.ext h)
    simp [Ne.symm he, hv]

theorem outputWords_value {m n : ℕ} (d : Data m n) (k : ℕ) (i : Fin n) (port : Fin 4)
    (hp : ((values d.records k).positive i).bits.length ≤ addressValue d.width)
    (hn : ((values d.records k).negative i).bits.length ≤ addressValue d.width) :
    addressValue ((outputWords d k port).get i) =
      if port = 0 ∨ port = 2 then (values d.records k).positive i
      else (values d.records k).negative i := by
  change addressValue (outputWords d k port)[i.val] = _
  simp only [outputWords, Vector.getElem_ofFn]
  split_ifs <;> rw [FixedWidth.bits_value _ _ (by assumption), addressValue_bits]

end Maxwell.Cost.CalibrationMatrix.SourceInit
