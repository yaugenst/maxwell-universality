import Maxwell.Cost.RealSparse
import Maxwell.Cost.RealSimulation.ControlCorrectness

/-! Addressed sparse records. Coefficients occupy consecutive real cells;
row and column labels occupy paired natural cells. -/
namespace Maxwell.Cost.RealSparseOrder
open RealSparse (entryAt)

structure Buffer where
  coefficients : ℕ
  coordinates : ℕ

def Buffer.row (b : Buffer) (i : ℕ) := b.coordinates+2*i
def Buffer.column (b : Buffer) (i : ℕ) := b.coordinates+2*i+1
def Buffer.value (b : Buffer) (i : ℕ) := b.coefficients+i

def StoredPrefix (b : Buffer) (s : RAMState) (entries : List SparseEntry) (count : ℕ) : Prop :=
  ∀ i < count, s.indices (b.row i) = (entryAt entries i).row ∧
    s.indices (b.column i) = (entryAt entries i).column ∧
    s.words (b.value i) = (entryAt entries i).value

def Stored (b : Buffer) (s : RAMState) (entries : List SparseEntry) : Prop :=
  StoredPrefix b s entries entries.length

def initialBuffer : Buffer := ⟨100,100⟩

end Maxwell.Cost.RealSparseOrder
