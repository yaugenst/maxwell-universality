import Maxwell.Cost.PositiveGraph.Fold
import Maxwell.Cost.PositiveGraph.Encoding

namespace Maxwell.Cost.PositiveGraph.Invariant

def diagonalWords {n : ℕ} (values : Vector ℤ n) : Vector (List Bool) n :=
  values.map fun a => FixedWidth.bits 4 (diagonalCode a).bits

@[simp] theorem diagonalWords_get {n : ℕ} (values : Vector ℤ n) (i : Fin n) :
    (diagonalWords values).get i = FixedWidth.bits 4 (diagonalCode (values.get i)).bits := by
  simp [diagonalWords,Vector.get,Fin.cast]

@[simp] theorem diagonalWords_value {n : ℕ} (values : Vector ℤ n) (i : Fin n) :
    codeAt (diagonalWords values) i = diagonalCode (values.get i) := by
  rw [codeAt,diagonalWords_get]
  exact IncidenceEncoding.word_value 4 _ (diagonalCode_lt _)

theorem updated_diagonalCode (a : ℤ) (negative half mediator : Bool) :
    DiagonalWord.updated (diagonalCode a) negative half mediator =
      diagonalCode (a+DiagonalWord.delta negative half mediator) := by
  unfold DiagonalWord.updated diagonalCode
  have h := Int.emod_nonneg (8+a) (by norm_num : (16:ℤ) ≠ 0)
  rw [Int.toNat_of_nonneg h]
  congr 1
  omega

def integerNext (d K k : ℕ) (hk : k<K) (e : BoundedEntry d)
    (values : Vector ℤ (2*d+K)) : Vector ℤ (2*d+K) :=
  let r := rowIndex d K e.val e.property.1
  let c := columnIndex d K e.val e.property.2
  let m := mediatorIndex d K k hk
  let negative := decide (e.val.value<0)
  let half := decide (e.val.value=1/2 ∨ e.val.value= -1/2)
  ((values.set r (values.get r+DiagonalWord.delta negative half false)).set c
    (values.get c+DiagonalWord.delta negative half false)).set m
    (values.get m+DiagonalWord.delta negative half true)

theorem nextDiagonal_encoded (d K k : ℕ) (hk : k<K) (e : BoundedEntry d)
    (values : Vector ℤ (2*d+K)) :
    nextDiagonal d K k hk e.val e.property.1 e.property.2 (diagonalWords values) =
      diagonalWords (integerNext d K k hk e values) := by
  simp only [nextDiagonal,TripleScatter.updated,diagonalWords_value,DiagonalUpdate.payload,updated_diagonalCode]
  simp only [integerNext,diagonalWords,Vector.map_set]

def integerFold (d K start : ℕ) (entries : List (BoundedEntry d))
    (hfit : start+entries.length ≤ K) (values : Vector ℤ (2*d+K)) : Vector ℤ (2*d+K) :=
  match entries with
  | [] => values
  | e::rest => integerFold d K (start+1) rest (by simp only [List.length_cons] at hfit; omega)
      (integerNext d K start (by simp only [List.length_cons] at hfit; omega) e values)

theorem fold_diagonal_encoded (W d K start : ℕ) (entries : List (BoundedEntry d))
    (hfit : start+entries.length ≤ K) (tables : Tables d K) (values : Vector ℤ (2*d+K))
    (hdiag : tables.diagonal=diagonalWords values) :
    (foldTables W d K start entries hfit tables).diagonal =
      diagonalWords (integerFold d K start entries hfit values) := by
  induction entries generalizing start tables values with
  | nil => exact hdiag
  | cons e rest ih =>
    simp only [foldTables,integerFold]
    apply ih
    change nextDiagonal d K start _ e.val e.property.1 e.property.2 tables.diagonal = _
    rw [hdiag,nextDiagonal_encoded]

end Maxwell.Cost.PositiveGraph.Invariant
