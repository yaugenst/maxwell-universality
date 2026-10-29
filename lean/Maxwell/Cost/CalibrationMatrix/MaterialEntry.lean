import Maxwell.Cost.CalibrationMatrix.MaterialTable
import Maxwell.Cost.CalibrationMatrix.TableKey

/-! Actual fixed-table emission of the signed stencil matrix numerator. -/
namespace Maxwell.Cost.CalibrationMatrix.MaterialEntry
open Structured RationalAccumulator
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

/-- This table is fixed by the platform. Its leaves contain exact canonical
integer channels, including all cancellation among the eighteen terms. -/
def table (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (bits : List Bool) : ℕ × ℕ :=
  entryChannels material z D (TableKey.decode bits)

def code (keyTape : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  MaterialTable.code keyTape 30 31 34 (table material z D)

def costBound (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : ℕ :=
  286 + 10 * MaterialTable.outputBits 34 (table material z D)

/-- Once the finite local key has been generated, ordinary Boolean reads
and literal writes emit exactly the two arrays consumed by dense matvec. -/
theorem executes {n : ℕ} (edges : Fin n → Edge) (material : Cell20 → ℚ)
    (z : ℚ) (D : ℕ) (i j : Fin n) (keyTape : ℕ) (hk30 : keyTape ≠ 30) (hk31 : keyTape ≠ 31)
    (input : List Bool) (randomTape : ℕ → Bool) (origin : ℤ) (s : Store)
    (hkey : s.val.tapes keyTape = BitTape.shifted
      (TableKey.encode (entryKey (edges i) (edges j))) origin)
    (h30 : Blank s.val 30) (h31 : Blank s.val 31) :
    ∃ cost t, cost ≤ costBound material z D ∧
      Executes input randomTape (code keyTape material z D) cost s t ∧
      Word t.val 30 ((integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).positive i j) ∧
      Word t.val 31 ((integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).negative i j) ∧
      t.val.tapes keyTape = {BitTape.blank with head := origin + 34} ∧
      MaterialTable.Frame keyTape 30 31 s.val t.val := by
  let key := entryKey (edges i) (edges j)
  obtain ⟨t, he, hp, hn, hk, hf⟩ := MaterialTable.executes keyTape 30 31 hk30 hk31
    (by decide) input randomTape (TableKey.encode key) (table material z D) origin s hkey h30 h31
  have htable : table material z D (TableKey.encode key) =
      ((integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).positive i j,
       (integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).negative i j) := by
    rw [table, TableKey.decode_encode]
    exact entryChannels_binding edges material z D i j
  have hb := MaterialTable.fixed_cost_bound (TableKey.encode key) (table material z D)
  refine ⟨8 * 34 + 10 * ((table material z D (TableKey.encode key)).1.size +
    (table material z D (TableKey.encode key)).2.size) + 14, t, ?_, ?_, ?_, ?_, ?_, hf⟩
  · simp only [TableKey.encode_length] at hb
    dsimp only [costBound]
    omega
  · simpa only [code, TableKey.encode_length] using he
  · simpa only [htable] using hp
  · simpa only [htable] using hn
  · simpa only [TableKey.encode_length, Nat.cast_ofNat] using hk

end Maxwell.Cost.CalibrationMatrix.MaterialEntry
