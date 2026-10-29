import Maxwell.Composition.BasisDefectLayout

/-! Full PEC box and all-cell material bounds after the actual fixed
integer lattice-basis transformation. -/
noncomputable section
namespace Maxwell.Composition.BasisDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil
open Maxwell.Logical.Routing

variable (S : Source.SparseSystem) (precision : ℕ) (B : Matrix Direction Direction ℤ)

theorem disjoint_cells (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing) :
    Pairwise (fun i j => Disjoint (cellBlocks S precision B D macroSpacing buffer i)
      (cellBlocks S precision B D macroSpacing buffer j)) := by
  classical
  exact blocks_disjoint _ D (position S precision B) _ _
    ((latticeCell_injective _).comp (indices_injective S precision B hB))
    _ (SourceDefectLayout.radius_bounds D) hspacing

theorem all_cells_retained (D : Finset Site) (macroSpacing buffer : ℕ)
    (i : SourceRouting.Vertex S precision) :
    (cellBlocks S precision B D macroSpacing buffer i).image Target.latticeCell =
      cells D ((20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer i) := by
  rw [← anchor_period]
  exact cellBlock_image _ _ (buffered_cells_inside (baseBox S precision B) (indices S precision B)
    D (SourceDefectLayout.radius D) (20 * macroSpacing) buffer (SourceDefectLayout.radius_bounds D) i)

theorem boundary_margin (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) (k : Direction) :
    let e := Target.latticeEdge (physicalBox S precision B D macroSpacing buffer)
      ((layout S precision B hB D macroSpacing buffer hspacing).pick ij)
    (buffer : ℤ) + 1 ≤ e.2 k ∧ e.2 k + ((buffer : ℤ) + 1) ≤
      (Green.boxSide (physicalBox S precision B D macroSpacing buffer) k : ℤ) := by
  dsimp only
  rw [lattice_pick, ← anchor_period]
  exact buffered_pick_margin (baseBox S precision B) (indices S precision B) D
    (SourceDefectLayout.radius D) (20 * macroSpacing) buffer (SourceDefectLayout.radius_bounds D) ij k

def material (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (background : (physicalBox S precision B D macroSpacing buffer).Cell → ℚ)
    (v : SourceRouting.Vertex S precision → ℚ) (headroom : ℚ) (hh : 0 ≤ headroom)
    (hbase : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - headroom)
    (hv : ∀ i, 0 ≤ v i ∧ 64 * v i ≤ headroom) :
    ScalarMaterial (physicalBox S precision B D macroSpacing buffer).nx
      (physicalBox S precision B D macroSpacing buffer).ny
      (physicalBox S precision B D macroSpacing buffer).nz := by
  classical
  exact ⟨Target.assembledMaterial background (cellBlocks S precision B D macroSpacing buffer) v,
    Target.assembledMaterial_bounds _ _ _ headroom hh hbase hv
      (disjoint_cells S precision B hB D macroSpacing buffer hspacing)⟩

theorem material_operator (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (background : (physicalBox S precision B D macroSpacing buffer).Cell → ℚ)
    (v : SourceRouting.Vertex S precision → ℚ) (headroom : ℚ) (hh : 0 ≤ headroom)
    (hbase : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - headroom)
    (hv : ∀ i, 0 ≤ v i ∧ 64 * v i ≤ headroom) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((Target.operator (physicalBox S precision B D macroSpacing buffer)
        (material S precision B hB D macroSpacing buffer hspacing background v headroom hh hbase hv).value).map Rat.cast) =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((Target.operator (physicalBox S precision B D macroSpacing buffer) background).map Rat.cast) -
      (coordinateExtension (layout S precision B hB D macroSpacing buffer hspacing).pick).comp
        ((blockDiagonal (fun ij => ((v ij.1 * ScalarDefect.coordinateWeight D ij.2 : ℚ) : ℝ))).comp
          (coordinateRestriction (layout S precision B hB D macroSpacing buffer hspacing).pick)) := by
  classical
  have h := (layout S precision B hB D macroSpacing buffer hspacing).operator_factorization background v
  simpa only [material, shared_weight] using h

def sideBudget (D : Finset Site) (macroSpacing buffer : ℕ) : ℕ :=
  20 * macroSpacing * (358 * coefficientSize B + 1) +
    40 * (SourceDefectLayout.radius D + buffer + 2)

theorem source_extent_le : extent (SourceDefectLayout.baseBox S precision) B ≤
    179 * coefficientSize B * SourceRouting.side S precision := by
  have hq := SourceRouting.side_pos S precision
  have hc : coefficientSize B ≤ coefficientSize B * SourceRouting.side S precision :=
    Nat.le_mul_of_pos_right _ hq
  dsimp [extent, SourceDefectLayout.baseBox, boxSideXY, boxSideZ]
  nlinarith

theorem physical_side_le (D : Finset Site) (macroSpacing buffer : ℕ) (k : Direction) :
    Green.boxSide (physicalBox S precision B D macroSpacing buffer) k ≤
      sideBudget B D macroSpacing buffer * SourceRouting.side S precision := by
  have hq := SourceRouting.side_pos S precision
  have he := source_extent_le S precision B
  have hbase : Green.boxSide (baseBox S precision B) k ≤
      (358 * coefficientSize B + 1) * SourceRouting.side S precision := by
    fin_cases k <;> dsimp [Green.boxSide, baseBox, transformedBox] <;> nlinarith
  have hm := Nat.mul_le_mul_left (20 * macroSpacing) hbase
  have hp : 40 * (SourceDefectLayout.radius D + buffer + 2) ≤
      40 * (SourceDefectLayout.radius D + buffer + 2) * SourceRouting.side S precision :=
    Nat.le_mul_of_pos_right _ hq
  change Green.boxSide (bufferedBox _ _ _ _) k ≤ _
  rw [bufferedBox_side]
  dsimp [sideBudget]
  nlinarith

theorem physical_cell_card_le (D : Finset Site) (macroSpacing buffer : ℕ) :
    Fintype.card (physicalBox S precision B D macroSpacing buffer).Cell ≤
      (sideBudget B D macroSpacing buffer * SourceRouting.side S precision) ^ 3 := by
  have h0 := physical_side_le S precision B D macroSpacing buffer 0
  have h1 := physical_side_le S precision B D macroSpacing buffer 1
  have h2 := physical_side_le S precision B D macroSpacing buffer 2
  dsimp [Green.boxSide] at h0 h1 h2
  change Fintype.card (Fin _ × Fin _ × Fin _) ≤ _
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ (sideBudget B D macroSpacing buffer * SourceRouting.side S precision) *
        ((sideBudget B D macroSpacing buffer * SourceRouting.side S precision) *
          (sideBudget B D macroSpacing buffer * SourceRouting.side S precision)) :=
      Nat.mul_le_mul h0 (Nat.mul_le_mul h1 h2)
    _ = _ := by ring

theorem physical_edge_card_le (D : Finset Site) (macroSpacing buffer : ℕ) :
    Fintype.card (physicalBox S precision B D macroSpacing buffer).Edge ≤
      3 * (sideBudget B D macroSpacing buffer * SourceRouting.side S precision) ^ 3 := by
  have hc := physical_cell_card_le S precision B D macroSpacing buffer
  let box := physicalBox S precision B D macroSpacing buffer
  have ha : box.nx * (box.ny - 1) * (box.nz - 1) ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hb : (box.nx - 1) * box.ny * (box.nz - 1) ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hd : (box.nx - 1) * (box.ny - 1) * box.nz ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
  change Fintype.card box.Edge ≤ _
  rw [retainedEdge_card]
  have hcells : Fintype.card box.Cell = box.nx * box.ny * box.nz := by
    simp [Target.Box.Cell, Maxwell.Cell, Nat.mul_assoc]
  change Fintype.card box.Cell ≤ _ at hc
  rw [hcells] at hc
  omega

end Maxwell.Composition.BasisDefectLayout
