import Maxwell.Cost.PositiveGraph.Step

namespace Maxwell.Cost.PositiveGraph

abbrev BoundedEntry (dimension : ℕ) :=
  {e : Logical.RationalCode.Entry // e.row < dimension ∧ e.column < dimension}

structure Tables (dimension count : ℕ) where
  endpoints : Vector (List Bool) (4*count)
  diagonal : Vector (List Bool) (2*dimension+count)

def Tables.next (width dimension count index : ℕ) (hi : index < count)
    (e : BoundedEntry dimension) (tables : Tables dimension count) : Tables dimension count :=
  ⟨nextEndpoints width dimension count index hi e.val tables.endpoints,
    nextDiagonal dimension count index hi e.val e.property.1 e.property.2 tables.diagonal⟩

structure Tables.Represents {dimension count : ℕ} (tables : Tables dimension count)
    (width base : ℕ) (memory : ℕ → Bool) : Prop where
  endpoints : BitArray.Represents memory 0 (width+3) tables.endpoints
  diagonal : BitArray.Represents memory base 4 tables.diagonal

def foldTables (width dimension count index : ℕ) (entries : List (BoundedEntry dimension))
    (hfit : index+entries.length ≤ count) (tables : Tables dimension count) : Tables dimension count :=
  match entries with
  | [] => tables
  | e::rest => foldTables width dimension count (index+1) rest (by simp only [List.length_cons] at hfit; omega)
      (tables.next width dimension count index (by simp only [List.length_cons] at hfit; omega) e)

def foldMemory (width dimension count index base : ℕ) (entries : List (BoundedEntry dimension))
    (hfit : index+entries.length ≤ count) (tables : Tables dimension count) (memory : ℕ → Bool) : ℕ → Bool :=
  match entries with
  | [] => memory
  | e::rest => foldMemory width dimension count (index+1) base rest (by simp only [List.length_cons] at hfit; omega)
      (tables.next width dimension count index (by simp only [List.length_cons] at hfit; omega) e)
      (entryMemory width dimension count index base (by simp only [List.length_cons] at hfit; omega)
        e.val e.property.1 e.property.2 tables.diagonal memory)

def foldPrice (width dimension count index base : ℕ) (clock : List Bool)
    (entries : List (BoundedEntry dimension)) (hfit : index+entries.length ≤ count)
    (tables : Tables dimension count) : ℕ :=
  match entries with
  | [] => 1
  | e::rest =>
    let hi : index < count := by simp only [List.length_cons] at hfit; omega
    Step.price width dimension count index base e.val clock
      (codeAt tables.diagonal (rowIndex dimension count e.val e.property.1))
      (codeAt tables.diagonal (columnIndex dimension count e.val e.property.2))
      (codeAt tables.diagonal (mediatorIndex dimension count index hi)) + 4 +
    foldPrice width dimension count (index+1) base clock rest (by simp only [List.length_cons] at hfit; omega)
      (tables.next width dimension count index hi e)

def recordsWire (width : ℕ) {dimension : ℕ} (entries : List (BoundedEntry dimension)) : List Bool :=
  SparseEmission.entriesWire width (entries.map Subtype.val)

@[simp] theorem recordsWire_nil (width dimension : ℕ) : recordsWire width ([] : List (BoundedEntry dimension)) = [] := rfl
@[simp] theorem recordsWire_cons (width : ℕ) {dimension : ℕ}
    (e : BoundedEntry dimension) (entries : List (BoundedEntry dimension)) :
    recordsWire width (e::entries) = SparseEmission.entryWire width e.val++recordsWire width entries := rfl

@[simp] theorem recordsWire_length (width : ℕ) {dimension : ℕ} (entries : List (BoundedEntry dimension)) :
    (recordsWire width entries).length = entries.length*(2*width+2) := by
  simp [recordsWire]

end Maxwell.Cost.PositiveGraph
