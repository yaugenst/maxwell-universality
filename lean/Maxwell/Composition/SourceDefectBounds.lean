import Maxwell.Composition.SourceDefectLayout

/-! Explicit material-placement and full-box resource bounds for the
constructed source-dependent defect layout. -/
noncomputable section
namespace Maxwell.Composition.SourceDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil
open Maxwell.Logical.Routing

/-- Direct finite insertion of each prototype cell; an emitter can iterate
these fixed-size prototype stencils over the routed vertices. -/
def cellPlacement (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) (c : D) :
    (physicalBox S precision D macroSpacing buffer).Cell :=
  finiteCell (physicalBox S precision D macroSpacing buffer)
    (anchor (position S precision) (20 * macroSpacing) (bufferedShift (radius D) buffer) i + c)
    (buffered_cells_inside (baseBox S precision) (indices S precision) D (radius D)
      (20 * macroSpacing) buffer (radius_bounds D) i _
      (Finset.mem_image.mpr ⟨c, c.property, rfl⟩))

@[simp] theorem lattice_cellPlacement (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) (c : D) :
    Target.latticeCell (cellPlacement S precision D macroSpacing buffer i c) =
      (20 : ℤ) • conventionalAnchor S precision D macroSpacing buffer i + c := by
  unfold cellPlacement physicalBox
  rw [lattice_finiteCell, anchor_period]

theorem cellPlacement_mem (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) (c : D) :
    cellPlacement S precision D macroSpacing buffer i c ∈
      cellBlocks S precision D macroSpacing buffer i := by
  change cellPlacement S precision D macroSpacing buffer i c ∈ cellBlock _ _
  rw [mem_cellBlock, lattice_cellPlacement, anchor_period]
  exact (mem_cells D _ c).mpr c.property

theorem cellPlacement_image (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (i : SourceRouting.Vertex S precision) :
    Finset.univ.image (cellPlacement S precision D macroSpacing buffer i) =
      cellBlocks S precision D macroSpacing buffer i := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact cellPlacement_mem _ _ _ _ _ _ _
  · intro hc
    have hc' : Target.latticeCell c ∈ cells D
        ((20 : ℤ) • conventionalAnchor S precision D macroSpacing buffer i) := by
      rw [← all_cells_retained]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc'
    refine Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, (latticeCell_injective _ ) ?_⟩
    simpa only [lattice_cellPlacement] using hae

theorem cellPlacement_injective (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (hspacing : 2 * (radius D + 1) < 20 * macroSpacing) :
    Function.Injective (fun ic : SourceRouting.Vertex S precision × D =>
      cellPlacement S precision D macroSpacing buffer ic.1 ic.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  change cellPlacement S precision D macroSpacing buffer i a =
    cellPlacement S precision D macroSpacing buffer j b at h
  have hij : i = j := by
    by_contra hne
    have hb := cellPlacement_mem S precision D macroSpacing buffer j b
    rw [← h] at hb
    exact Finset.disjoint_left.mp (disjoint_cells S precision D macroSpacing buffer hspacing hne)
      (cellPlacement_mem _ _ _ _ _ _ a) hb
  subst j
  have hc := congrArg Target.latticeCell h
  simp only [lattice_cellPlacement] at hc
  exact Prod.ext rfl (Subtype.ext (add_left_cancel hc))

/-- A single literal coefficient bounds each padded physical side by the
original routing side. It is polynomial in spacing and logarithmic buffer. -/
def sideBudget (D : Finset Site) (macroSpacing buffer : ℕ) : ℕ :=
  2580 * macroSpacing + 40 * (radius D + buffer + 2)

theorem physical_side_le (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) (k : Direction) :
    Green.boxSide (physicalBox S precision D macroSpacing buffer) k ≤
      sideBudget D macroSpacing buffer * SourceRouting.side S precision := by
  have hq := SourceRouting.side_pos S precision
  have hp : 40 * (radius D + buffer + 2) ≤
      40 * (radius D + buffer + 2) * SourceRouting.side S precision := by
    exact Nat.le_mul_of_pos_right _ hq
  have hd : macroSpacing ≤ macroSpacing * SourceRouting.side S precision :=
    Nat.le_mul_of_pos_right _ hq
  fin_cases k <;>
    dsimp [physicalBox, bufferedBox, Green.boxSide, baseBox, boxSideXY, boxSideZ, sideBudget] <;> nlinarith

theorem physical_cell_card_le (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) :
    Fintype.card (physicalBox S precision D macroSpacing buffer).Cell ≤
      (sideBudget D macroSpacing buffer * SourceRouting.side S precision) ^ 3 := by
  have h0 := physical_side_le S precision D macroSpacing buffer 0
  have h1 := physical_side_le S precision D macroSpacing buffer 1
  have h2 := physical_side_le S precision D macroSpacing buffer 2
  dsimp [Green.boxSide] at h0 h1 h2
  change Fintype.card (Fin _ × Fin _ × Fin _) ≤ _
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ (sideBudget D macroSpacing buffer * SourceRouting.side S precision) *
        ((sideBudget D macroSpacing buffer * SourceRouting.side S precision) *
          (sideBudget D macroSpacing buffer * SourceRouting.side S precision)) :=
      Nat.mul_le_mul h0 (Nat.mul_le_mul h1 h2)
    _ = _ := by ring

theorem physical_edge_card_le (S : Source.SparseSystem) (precision : ℕ) (D : Finset Site)
    (macroSpacing buffer : ℕ) :
    Fintype.card (physicalBox S precision D macroSpacing buffer).Edge ≤
      3 * (sideBudget D macroSpacing buffer * SourceRouting.side S precision) ^ 3 := by
  have hc := physical_cell_card_le S precision D macroSpacing buffer
  let B := physicalBox S precision D macroSpacing buffer
  have ha : B.nx * (B.ny - 1) * (B.nz - 1) ≤ B.nx * B.ny * B.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hb : (B.nx - 1) * B.ny * (B.nz - 1) ≤ B.nx * B.ny * B.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hd : (B.nx - 1) * (B.ny - 1) * B.nz ≤ B.nx * B.ny * B.nz :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
  change Fintype.card B.Edge ≤ _
  rw [retainedEdge_card]
  have hcells : Fintype.card B.Cell = B.nx * B.ny * B.nz := by
    simp [Target.Box.Cell, Maxwell.Cell, Nat.mul_assoc]
  change Fintype.card B.Cell ≤ _ at hc
  rw [hcells] at hc
  omega

end Maxwell.Composition.SourceDefectLayout
