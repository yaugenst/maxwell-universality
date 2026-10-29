import Maxwell.Composition.BasisDefectBounds
import Maxwell.Composition.SourceDecoration

/-! The full physical terminal--mediator set, transformed by the certified
integer basis and placed as disjoint period-twenty scalar defect stencils. -/
noncomputable section
namespace Maxwell.Composition.DecoratedDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil Maxwell.Composition.BasisDefectLayout
open scoped BigOperators

section Source
variable (S : Source.SparseSystem) (precision : ℕ) (B : Matrix Direction Direction ℤ)

def baseBox : Target.Box := transformedBox (SourceDecoration.baseBox S precision) B

def indices : SourceDecoration.Vertex S precision → (baseBox S precision B).Cell :=
  fun i => transformedIndex _ B (SourceDecoration.indices S precision i)

theorem indices_injective (hB : Function.Injective B.mulVec) :
    Function.Injective (indices S precision B) :=
  (transformedIndex_injective _ B hB).comp (SourceDecoration.indices_injective _ _)

def position : SourceDecoration.Vertex S precision → Site :=
  fun i => Target.latticeCell (indices S precision B i)

def physicalBox (D : Finset Site) (macroSpacing buffer : ℕ) : Target.Box :=
  bufferedBox (baseBox S precision B) (SourceDefectLayout.radius D) (20 * macroSpacing) buffer

def conventionalAnchor (D : Finset Site) (macroSpacing buffer : ℕ)
    (i : SourceDecoration.Vertex S precision) : Site :=
  (fun _ : Direction => ((SourceDefectLayout.radius D + buffer + 1 : ℕ) : ℤ)) +
    (macroSpacing : ℤ) • position S precision B i

theorem anchor_period (D : Finset Site) (macroSpacing buffer : ℕ)
    (i : SourceDecoration.Vertex S precision) :
    anchor (position S precision B) (20 * macroSpacing)
      (bufferedShift (SourceDefectLayout.radius D) buffer) i =
      (20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer i := by
  ext k
  simp [anchor, bufferedShift, conventionalAnchor]
  ring

/-- The block separation is exactly the certified integer basis applied to
the actual routed lattice displacement, including its orientation. -/
theorem anchor_difference (D : Finset Site) (macroSpacing buffer : ℕ)
    (i j : SourceDecoration.Vertex S precision) :
    conventionalAnchor S precision B D macroSpacing buffer i -
      conventionalAnchor S precision B D macroSpacing buffer j =
      (macroSpacing : ℤ) • B.mulVec
        (SourceDecoration.site S precision i - SourceDecoration.site S precision j) := by
  have h : position S precision B i - position S precision B j =
      B.mulVec (SourceDecoration.site S precision i - SourceDecoration.site S precision j) := by
    change Target.latticeCell (transformedIndex _ B (SourceDecoration.indices S precision i)) -
      Target.latticeCell (transformedIndex _ B (SourceDecoration.indices S precision j)) = _
    rw [transformedIndex_lattice, transformedIndex_lattice]
    simpa only [SourceDecoration.indices_lattice] using
      transformedPosition_sub _ B (SourceDecoration.indices S precision i) (SourceDecoration.indices S precision j)
  rw [← h, smul_sub]
  simp only [conventionalAnchor]
  abel

def cellBlocks (D : Finset Site) (macroSpacing buffer : ℕ) :
    SourceDecoration.Vertex S precision → Finset (physicalBox S precision B D macroSpacing buffer).Cell :=
  blocks (physicalBox S precision B D macroSpacing buffer) D (position S precision B)
    (20 * macroSpacing) (bufferedShift (SourceDefectLayout.radius D) buffer)

theorem inside (D : Finset Site) (macroSpacing buffer : ℕ)
    (ij : SourceDecoration.Vertex S precision × Fin (ScalarDefect.edges D).card) (k : Direction) :
    0 < (pick D (position S precision B) (20 * macroSpacing)
      (bufferedShift (SourceDefectLayout.radius D) buffer) ij).2 k ∧
      (pick D (position S precision B) (20 * macroSpacing)
        (bufferedShift (SourceDefectLayout.radius D) buffer) ij).2 k <
        (Green.boxSide (physicalBox S precision B D macroSpacing buffer) k : ℤ) :=
  buffered_pick_inside (baseBox S precision B) (indices S precision B) D (SourceDefectLayout.radius D)
    (20 * macroSpacing) buffer (SourceDefectLayout.radius_bounds D) ij k

def layout (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing) :
    DefectLayout (κ := Fin (ScalarDefect.edges D).card) (cellBlocks S precision B D macroSpacing buffer) := by
  classical
  exact bufferedLayout (baseBox S precision B) (indices S precision B) (indices_injective S precision B hB)
    D (SourceDefectLayout.radius D) (20 * macroSpacing) buffer (SourceDefectLayout.radius_bounds D) hspacing

theorem shared_weight (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (ij : SourceDecoration.Vertex S precision × Fin (ScalarDefect.edges D).card) :
    (layout S precision B hB D macroSpacing buffer hspacing).weight ij =
      ScalarDefect.coordinateWeight D ij.2 := by
  classical
  exact layout_weight _ D (position S precision B) (20 * macroSpacing)
    (bufferedShift (SourceDefectLayout.radius D) buffer)
    ((latticeCell_injective _).comp (indices_injective S precision B hB))
    _ (SourceDefectLayout.radius_bounds D) hspacing (inside S precision B D macroSpacing buffer) ij

theorem lattice_pick (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (ij : SourceDecoration.Vertex S precision × Fin (ScalarDefect.edges D).card) :
    Target.latticeEdge (physicalBox S precision B D macroSpacing buffer)
      ((layout S precision B hB D macroSpacing buffer hspacing).pick ij) =
      edge ((20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer ij.1)
        (ScalarDefect.edgeEmbedding D ij.2) := by
  classical
  change Target.latticeEdge _ (finitePick _ D (position S precision B) (20 * macroSpacing)
    (bufferedShift (SourceDefectLayout.radius D) buffer) (inside S precision B D macroSpacing buffer) ij) = _
  rw [lattice_finitePick]
  simp only [pick, anchor_period]

end Source
end Maxwell.Composition.DecoratedDefectLayout
