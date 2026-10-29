import Maxwell.Green.CalibrationInteger
import Maxwell.Green.CalibrationIndex

/-! The finite, translation-independent key of an actual stencil entry. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def translateEdge (x : Site) (e : Edge) : Edge := (e.1, e.2 + x)
def translateSparse (x : Site) (v : SparseField) : SparseField :=
  v.map fun t => (translateEdge x t.1, t.2)

private theorem translate_scale (x : Site) (q : ℚ) (v : SparseField) :
    translateSparse x (scale q v) = scale q (translateSparse x v) := by
  simp only [translateSparse, scale, List.map_map]
  rfl

private theorem translate_append (x : Site) (u v : SparseField) :
    translateSparse x (u ++ v) = translateSparse x u ++ translateSparse x v := by
  simp only [translateSparse, List.map_append]

private theorem translate_pullback (x : Site) (p : Equiv.Perm Direction)
    (v : Direction → Site) (w : SparseField) :
    translateSparse x (pullback (fieldPermutation p v) w) =
      pullback (fieldPermutation p v) (translateSparse x w) := by
  simp only [translateSparse, pullback, List.map_map]
  apply List.map_congr_left
  intro t _
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (t.1.2 - v (p.symm t.1.1)) + x = (t.1.2 + x) - v (p.symm t.1.1)
      abel
  · rfl

private theorem translate_pullback_symm (x : Site) (p : Equiv.Perm Direction)
    (v : Direction → Site) (w : SparseField) :
    translateSparse x (pullback (fieldPermutation p v).symm w) =
      pullback (fieldPermutation p v).symm (translateSparse x w) := by
  simp only [translateSparse, pullback, List.map_map]
  apply List.map_congr_left
  intro t _
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change (t.1.2 + v t.1.1) + x = (t.1.2 + x) + v t.1.1
      abel
  · rfl

private theorem translate_curl (x : Site) (v : SparseField) :
    translateSparse x (curl v) = curl (translateSparse x v) := by
  simp only [curl, translate_append, translate_scale, translate_pullback]

private theorem translate_curlAdjoint (x : Site) (v : SparseField) :
    translateSparse x (curlAdjoint v) = curlAdjoint (translateSparse x v) := by
  simp only [curlAdjoint, translate_append, translate_scale, translate_pullback_symm]

/-- The sixteen edge offsets and signs depend only on the direction. -/
theorem freeStencilTerms_translate (e : Edge) :
    freeStencilTerms e = translateSparse e.2 (freeStencilTerms (e.1, 0)) := by
  simp only [freeStencilTerms, translate_curlAdjoint, translate_curl]
  simp only [translateSparse, List.map_cons, List.map_nil, translateEdge, zero_add]

/-- A fixed table contains the four-cell average for each periodic edge. -/
def periodicMaterial (material : Cell20 → ℚ) (e : Edge20) : ℚ :=
  let p := PeriodicYee.transverseDirections e.1
  (material e.2 + material (e.2 - PeriodicYee.unitCell p.1) +
    material (e.2 - PeriodicYee.unitCell p.2) +
    material (e.2 - PeriodicYee.unitCell p.1 - PeriodicYee.unitCell p.2)) / 4

theorem periodicMaterial_binding (material : Cell20 → ℚ) (e : Edge) :
    periodicMaterial material (edgeMod20 e) = rationalEdgeAverage material e := rfl

/-- A stencil key has a fixed number of bits: a periodic edge, sixteen
local edge-equality decisions, and the diagonal equality decision. -/
@[ext] structure StencilKey where
  edge : Edge20
  hit : Fin 16 → Bool
  diagonal : Bool

/-- The sixteen tests compare an actual row edge to the translated fixed
curl-curl offsets of the column edge. -/
def entryKey (row column : Edge) : StencilKey where
  edge := edgeMod20 column
  hit k := decide (row = translateEdge column.2
    ((freeStencilTerms (column.1, 0))[k.val]'(by rw [freeStencilTerms_length]; exact k.isLt)).1)
  diagonal := decide (row = column)

/-- Fixed rational table value. Only the finite platform and the fixed
operating shift appear here; the cube radius is absent. -/
def entryValue (material : Cell20 → ℚ) (z : ℚ) (key : StencilKey) : ℚ :=
  (∑ k : Fin 16, if key.hit k then
    ((freeStencilTerms (key.edge.1, 0))[k.val]'(by rw [freeStencilTerms_length]; exact k.isLt)).2 else 0) -
    (if key.diagonal then periodicMaterial material key.edge / 64 + z else 0)

/-- Literal signed channels stored at each fixed decision-tree leaf. -/
def entryChannels (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (key : StencilKey) : ℕ × ℕ :=
  let a := commonNumerator D (entryValue material z key)
  (a.toNat, (-a).toNat)

private theorem list_sum_sixteen {α : Type*} (l : List α) (hl : l.length = 16)
    (f : α → ℚ) :
    (∑ k : Fin 16, f (l[k.val]'(by rw [hl]; exact k.isLt))) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [hl]
  · intro i hleft hright
    simp only [List.getElem_ofFn, List.getElem_map]

/-- The fixed table value is exactly the actual finite-section stencil
entry, including cancellation of repeated curl-curl edges. -/
theorem entryValue_binding {n : ℕ} (edges : Fin n → Edge)
    (material : Cell20 → ℚ) (z : ℚ) (i j : Fin n) :
    entryValue material z (entryKey (edges i) (edges j)) =
      stencilMatrix edges (rationalEdgeAverage material) z i j := by
  rw [stencilMatrix_entry_formula, freeStencilTerms_translate]
  unfold entryValue
  congr 1
  · simp only [entryKey, edgeMod20, decide_eq_true_eq]
    exact list_sum_sixteen (freeStencilTerms ((edges j).1, 0))
      (freeStencilTerms_length _) (fun t => if edges i = translateEdge (edges j).2 t.1 then t.2 else 0)
  · simp only [entryKey, decide_eq_true_eq, periodicMaterial_binding]

/-- Canonical positive and negative matrix arrays can be emitted directly
from the finite table; no run-time rational operation remains. -/
theorem entryChannels_binding {n : ℕ} (edges : Fin n → Edge)
    (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (i j : Fin n) :
    entryChannels material z D (entryKey (edges i) (edges j)) =
      ((integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).positive i j,
       (integerMatrix (stencilMatrix edges (rationalEdgeAverage material) z) D).negative i j) := by
  simp only [entryChannels, entryValue_binding, integerMatrix]

end Maxwell.Defect.FiniteStencil
