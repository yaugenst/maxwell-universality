import Maxwell.Composition.DecoratedDefectBounds

/-! Direct prototype-cell insertion for every physical terminal and mediator.
The emitted cells equal the full material block specification exactly. -/
noncomputable section
namespace Maxwell.Composition.DecoratedDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Composition.TranslatedStencil

variable (S : Source.SparseSystem) (precision : ℕ) (B : Matrix Direction Direction ℤ)
variable (D : Finset Site) (macroSpacing buffer : ℕ)

def cellPlacement (i : SourceDecoration.Vertex S precision) (c : D) :
    (physicalBox S precision B D macroSpacing buffer).Cell :=
  finiteCell (physicalBox S precision B D macroSpacing buffer)
    (anchor (position S precision B) (20 * macroSpacing)
      (bufferedShift (SourceDefectLayout.radius D) buffer) i + c)
    (buffered_cells_inside (baseBox S precision B) (indices S precision B) D (SourceDefectLayout.radius D)
      (20 * macroSpacing) buffer (SourceDefectLayout.radius_bounds D) i _
      (Finset.mem_image.mpr ⟨c, c.property, rfl⟩))

@[simp] theorem lattice_cellPlacement (i : SourceDecoration.Vertex S precision) (c : D) :
    Target.latticeCell (cellPlacement S precision B D macroSpacing buffer i c) =
      (20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer i + c := by
  unfold cellPlacement physicalBox
  rw [lattice_finiteCell, anchor_period]

theorem cellPlacement_mem (i : SourceDecoration.Vertex S precision) (c : D) :
    cellPlacement S precision B D macroSpacing buffer i c ∈
      cellBlocks S precision B D macroSpacing buffer i := by
  change cellPlacement S precision B D macroSpacing buffer i c ∈ cellBlock _ _
  rw [mem_cellBlock, lattice_cellPlacement, anchor_period]
  exact (mem_cells D _ c).mpr c.property

theorem cellPlacement_image (i : SourceDecoration.Vertex S precision) :
    Finset.univ.image (cellPlacement S precision B D macroSpacing buffer i) =
      cellBlocks S precision B D macroSpacing buffer i := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact cellPlacement_mem _ _ _ _ _ _ _ _
  · intro hc
    have hc' : Target.latticeCell c ∈ cells D
        ((20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer i) := by
      rw [← all_cells_retained]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc'
    refine Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, (latticeCell_injective _) ?_⟩
    simpa only [lattice_cellPlacement] using hae

theorem cellPlacement_injective (hB : Function.Injective B.mulVec)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing) :
    Function.Injective (fun ic : SourceDecoration.Vertex S precision × D =>
      cellPlacement S precision B D macroSpacing buffer ic.1 ic.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  change cellPlacement S precision B D macroSpacing buffer i a =
    cellPlacement S precision B D macroSpacing buffer j b at h
  have hij : i = j := by
    by_contra hne
    have hb := cellPlacement_mem S precision B D macroSpacing buffer j b
    rw [← h] at hb
    exact Finset.disjoint_left.mp (disjoint_cells S precision B hB D macroSpacing buffer hspacing hne)
      (cellPlacement_mem _ _ _ _ _ _ _ a) hb
  subst j
  have hc := congrArg Target.latticeCell h
  simp only [lattice_cellPlacement] at hc
  exact Prod.ext rfl (Subtype.ext (add_left_cancel hc))

end Maxwell.Composition.DecoratedDefectLayout
