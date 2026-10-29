import Maxwell.Composition.BufferedLayout
import Maxwell.Composition.SourceRouting

/-! Actual translated scalar defects at the vertices of the routed source
instance. Conventional-cell anchors preserve the period-twenty background.
The shared quarter-weight stencil and the complete finite material follow
from the emitted scalar cells. -/
noncomputable section
namespace Maxwell.Composition.SourceDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Logical.Routing
open Maxwell.Composition.TranslatedStencil
open scoped BigOperators

/-- A computable coordinate radius of the fixed finite prototype. -/
def radius (D : Finset Site) : ℕ := D.sup fun c => Finset.univ.sup fun k => (c k).natAbs

theorem radius_bounds (D : Finset Site) (c : Site) (hc : c ∈ D) (k : Direction) :
    -(radius D : ℤ) ≤ c k ∧ c k ≤ radius D := by
  have hk : (c k).natAbs ≤ radius D :=
    (Finset.le_sup (f := fun j : Direction => (c j).natAbs) (Finset.mem_univ k)).trans
      (Finset.le_sup (f := fun a : Site => Finset.univ.sup fun j => (a j).natAbs) hc)
  have habs : |c k| ≤ (radius D : ℤ) := by
    simpa only [Int.natCast_natAbs] using (show ((c k).natAbs : ℤ) ≤ radius D from by exact_mod_cast hk)
  exact abs_le.mp habs

def baseBox (S : Source.SparseSystem) (precision : ℕ) : Target.Box where
  nx := boxSideXY (SourceRouting.side S precision)
  ny := boxSideXY (SourceRouting.side S precision)
  nz := boxSideZ (SourceRouting.side S precision)

def indices (S : Source.SparseSystem) (precision : ℕ) :
    SourceRouting.Vertex S precision → (baseBox S precision).Cell :=
  SourceRouting.boxIndex S precision

theorem indices_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (indices S precision) := SourceRouting.boxIndex_injective _ _

def position (S : Source.SparseSystem) (precision : ℕ) :
    SourceRouting.Vertex S precision → Site := fun i => Target.latticeCell (indices S precision i)

theorem position_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (position S precision) :=
  (latticeCell_injective _).comp (indices_injective S precision)

/-- The conventional-cell coordinate; multiplication by twenty occurs only
when inserting the scalar prototype into the fine Yee lattice. -/
def conventionalAnchor (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) : Site :=
  (fun _ : Direction => ((radius D + buffer + 1 : ℕ) : ℤ)) + (macroSpacing : ℤ) • position S precision i

theorem anchor_period (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) :
    anchor (position S precision) (20 * macroSpacing) (bufferedShift (radius D) buffer) i =
      (20 : ℤ) • conventionalAnchor S precision D macroSpacing buffer i := by
  ext k
  simp [anchor, bufferedShift, conventionalAnchor]
  ring

theorem anchor_difference (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i j : SourceRouting.Vertex S precision) :
    conventionalAnchor S precision D macroSpacing buffer i -
      conventionalAnchor S precision D macroSpacing buffer j =
      (macroSpacing : ℤ) • (position S precision i - position S precision j) := by
  simp only [conventionalAnchor, smul_sub]
  abel

def physicalBox (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) : Target.Box :=
  bufferedBox (baseBox S precision) (radius D) (20 * macroSpacing) buffer

def cellBlocks (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) :
    SourceRouting.Vertex S precision → Finset (physicalBox S precision D macroSpacing buffer).Cell :=
  blocks (physicalBox S precision D macroSpacing buffer) D (position S precision)
    (20 * macroSpacing) (bufferedShift (radius D) buffer)

theorem inside (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) (k : Direction) :
    0 < (pick D (position S precision) (20 * macroSpacing) (bufferedShift (radius D) buffer) ij).2 k ∧
      (pick D (position S precision) (20 * macroSpacing) (bufferedShift (radius D) buffer) ij).2 k <
        (Green.boxSide (physicalBox S precision D macroSpacing buffer) k : ℤ) :=
  buffered_pick_inside (baseBox S precision) (indices S precision) D (radius D)
    (20 * macroSpacing) buffer (radius_bounds D) ij k

/-- The actual layout is built from the actual source circuit's routed graph. -/
def layout (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing) :
    DefectLayout (κ := Fin (ScalarDefect.edges D).card)
      (cellBlocks S precision D macroSpacing buffer) := by
  classical
  exact bufferedLayout (baseBox S precision) (indices S precision) (indices_injective _ _)
    D (radius D) (20 * macroSpacing) buffer (radius_bounds D) hspacing

theorem shared_weight (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) :
    (layout S precision D macroSpacing buffer hspacing).weight ij =
      ScalarDefect.coordinateWeight D ij.2 := by
  classical
  exact layout_weight (physicalBox S precision D macroSpacing buffer) D (position S precision)
    (20 * macroSpacing) (bufferedShift (radius D) buffer) (position_injective S precision)
    (radius D) (radius_bounds D) hspacing (inside S precision D macroSpacing buffer) ij

theorem lattice_pick (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) :
    Target.latticeEdge (physicalBox S precision D macroSpacing buffer)
      ((layout S precision D macroSpacing buffer hspacing).pick ij) =
      edge ((20 : ℤ) • conventionalAnchor S precision D macroSpacing buffer ij.1)
        (ScalarDefect.edgeEmbedding D ij.2) := by
  classical
  change Target.latticeEdge _ (finitePick _ D (position S precision) (20 * macroSpacing)
    (bufferedShift (radius D) buffer) (inside S precision D macroSpacing buffer) ij) = _
  rw [lattice_finitePick]
  simp only [pick, anchor_period]

theorem disjoint_cells (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing) :
    Pairwise (fun i j => Disjoint (cellBlocks S precision D macroSpacing buffer i)
      (cellBlocks S precision D macroSpacing buffer j)) := by
  classical
  exact blocks_disjoint _ D _ _ _ (position_injective S precision) _ (radius_bounds D) hspacing

theorem all_cells_retained (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) :
    (cellBlocks S precision D macroSpacing buffer i).image Target.latticeCell =
      cells D ((20 : ℤ) • conventionalAnchor S precision D macroSpacing buffer i) := by
  rw [← anchor_period]
  exact cellBlock_image _ _ (buffered_cells_inside (baseBox S precision) (indices S precision)
    D (radius D) (20 * macroSpacing) buffer (radius_bounds D) i)

theorem boundary_margin (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) (k : Direction) :
    let e := Target.latticeEdge (physicalBox S precision D macroSpacing buffer)
      ((layout S precision D macroSpacing buffer hspacing).pick ij)
    (buffer : ℤ) + 1 ≤ e.2 k ∧ e.2 k + ((buffer : ℤ) + 1) ≤
      (Green.boxSide (physicalBox S precision D macroSpacing buffer) k : ℤ) := by
  dsimp only
  rw [lattice_pick, ← anchor_period]
  exact buffered_pick_margin (baseBox S precision) (indices S precision) D (radius D)
    (20 * macroSpacing) buffer (radius_bounds D) ij k

/-- Emission has exactly the fixed prototype cell count per routed vertex. -/
theorem cellBlock_card (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) :
    (cellBlocks S precision D macroSpacing buffer i).card = D.card := by
  have h := congrArg Finset.card (all_cells_retained S precision D macroSpacing buffer i)
  rw [Finset.card_image_of_injective _ (latticeCell_injective _)] at h
  rw [cells, Finset.card_image_of_injective _ (fun a b h => add_left_cancel h)] at h
  exact h

/-- All-draw scalar headroom is checked at the actual emitted cell field. -/
def material (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing)
    (background : (physicalBox S precision D macroSpacing buffer).Cell → ℚ)
    (v : SourceRouting.Vertex S precision → ℚ) (headroom : ℚ) (hh : 0 ≤ headroom)
    (hbase : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - headroom)
    (hv : ∀ i, 0 ≤ v i ∧ 64 * v i ≤ headroom) :
    ScalarMaterial (physicalBox S precision D macroSpacing buffer).nx
      (physicalBox S precision D macroSpacing buffer).ny
      (physicalBox S precision D macroSpacing buffer).nz := by
  classical
  exact ⟨Target.assembledMaterial background (cellBlocks S precision D macroSpacing buffer) v,
    Target.assembledMaterial_bounds _ _ _ headroom hh hbase hv
      (disjoint_cells S precision D macroSpacing buffer hspacing)⟩

/-- The complete rational-output Maxwell operator has the shared physical
quarter-weight factorization, derived from its emitted scalar material. -/
theorem material_operator (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing)
    (background : (physicalBox S precision D macroSpacing buffer).Cell → ℚ)
    (v : SourceRouting.Vertex S precision → ℚ) (headroom : ℚ) (hh : 0 ≤ headroom)
    (hbase : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - headroom)
    (hv : ∀ i, 0 ≤ v i ∧ 64 * v i ≤ headroom) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((Target.operator (physicalBox S precision D macroSpacing buffer)
        (material S precision D macroSpacing buffer hspacing background v headroom hh hbase hv).value).map Rat.cast) =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((Target.operator (physicalBox S precision D macroSpacing buffer) background).map Rat.cast) -
      (coordinateExtension (layout S precision D macroSpacing buffer hspacing).pick).comp
        ((blockDiagonal (fun ij => ((v ij.1 * ScalarDefect.coordinateWeight D ij.2 : ℚ) : ℝ))).comp
          (coordinateRestriction (layout S precision D macroSpacing buffer hspacing).pick)) := by
  classical
  have h := (layout S precision D macroSpacing buffer hspacing).operator_factorization background v
  simpa only [material, shared_weight] using h

end Maxwell.Composition.SourceDefectLayout
