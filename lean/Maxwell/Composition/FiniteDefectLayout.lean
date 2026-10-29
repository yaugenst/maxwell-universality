import Maxwell.Composition.TranslatedStencil
import Maxwell.Composition.DefectCoordinates
import Maxwell.Green.BoundaryStrip

/-! The actual finite PEC realization of translated scalar-cell defects.
The four-cell averaging convention and coordinate support are derived from
`ScalarDefect`, including its deterministic finite edge enumeration. -/
noncomputable section
namespace Maxwell.Composition.TranslatedStencil
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open scoped BigOperators

/-- A direct conversion of an interior lattice edge to the retained PEC index. -/
def finiteEdge (B : Target.Box) (e : Edge)
    (hinside : ∀ i, 0 < e.2 i ∧ e.2 i < (Green.boxSide B i : ℤ)) : B.Edge := by
  have h0 := hinside 0
  have h1 := hinside 1
  have h2 := hinside 2
  simp [Green.boxSide] at h0 h1 h2
  exact if e.1 = 0 then Sum.inl (⟨(e.2 0).toNat, by omega⟩,
      ⟨(e.2 1 - 1).toNat, by omega⟩, ⟨(e.2 2 - 1).toNat, by omega⟩)
    else if e.1 = 1 then Sum.inr (Sum.inl (⟨(e.2 0 - 1).toNat, by omega⟩,
      ⟨(e.2 1).toNat, by omega⟩, ⟨(e.2 2 - 1).toNat, by omega⟩))
    else Sum.inr (Sum.inr (⟨(e.2 0 - 1).toNat, by omega⟩,
      ⟨(e.2 1 - 1).toNat, by omega⟩, ⟨(e.2 2).toNat, by omega⟩))

@[simp] theorem lattice_finiteEdge (B : Target.Box) (e : Edge)
    (hinside : ∀ i, 0 < e.2 i ∧ e.2 i < (Green.boxSide B i : ℤ)) :
    Target.latticeEdge B (finiteEdge B e hinside) = e := by
  rcases e with ⟨d, x⟩
  have h0 := (hinside 0).1
  have h1 := (hinside 1).1
  have h2 := (hinside 2).1
  change 0 < x 0 at h0
  change 0 < x 1 at h1
  change 0 < x 2 at h2
  fin_cases d
  · change (0, ![((x 0).toNat : ℤ), ((x 1 - 1).toNat : ℤ) + 1,
        ((x 2 - 1).toNat : ℤ) + 1]) = (0, x)
    congr 1
    ext k
    fin_cases k <;> simp <;> omega
  · change (1, ![((x 0 - 1).toNat : ℤ) + 1, ((x 1).toNat : ℤ),
        ((x 2 - 1).toNat : ℤ) + 1]) = (1, x)
    congr 1
    ext k
    fin_cases k <;> simp <;> omega
  · change (2, ![((x 0 - 1).toNat : ℤ) + 1, ((x 1 - 1).toNat : ℤ) + 1,
        ((x 2).toNat : ℤ)]) = (2, x)
    congr 1
    ext k
    fin_cases k <;> simp <;> omega

/-- Exact restriction of a finite scalar lattice cell set to the emitted box. -/
def cellBlock (B : Target.Box) (D : Finset Site) : Finset B.Cell :=
  Finset.univ.filter fun c => Target.latticeCell c ∈ D

@[simp] theorem mem_cellBlock (B : Target.Box) (D : Finset Site) (c : B.Cell) :
    c ∈ cellBlock B D ↔ Target.latticeCell c ∈ D := by simp [cellBlock]

/-- Finite and infinite quarter weights agree exactly, with no boundary
correction or replacement of a physical incident cell. -/
theorem weight_cellBlock (B : Target.Box) (D : Finset Site) (e : B.Edge) :
    Target.defectWeight (cellBlock B D) e = ScalarDefect.weight D (Target.latticeEdge B e) := by
  simp only [Target.defectWeight, edgeAverage, Target.defectIndicator, mem_cellBlock,
    ← Target.lattice_incidentCells, incidentCell_order]
  simp only [ScalarDefect.weight, ScalarDefect.edgeAverage, ScalarDefect.indicator,
    Fin.sum_univ_four]
  change (_ + _ + _ + _ : ℚ) / 4 = (_ + _ + _ + _ : ℚ) / 4
  have h0 : (0 : Fin 4).rev = 3 := rfl
  have h1 : (1 : Fin 4).rev = 2 := rfl
  have h2 : (2 : Fin 4).rev = 1 := rfl
  have h3 : (3 : Fin 4).rev = 0 := rfl
  rw [h0, h1, h2, h3]
  ring

section Layout
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (B : Target.Box) (D : Finset Site) (position : ι → Site) (spacing : ℕ) (shift : Site)

/-- The actual finite cell blocks, before applying their scalar strengths. -/
def blocks : ι → Finset B.Cell := fun i => cellBlock B (cells D (anchor position spacing shift i))

def finitePick
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ)) :
    ι × Fin (ScalarDefect.edges D).card → B.Edge :=
  fun ij => finiteEdge B (pick D position spacing shift ij) (hinside ij)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem lattice_finitePick
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ))
    (ij : ι × Fin (ScalarDefect.edges D).card) :
    Target.latticeEdge B (finitePick B D position spacing shift hinside ij) =
      pick D position spacing shift ij := lattice_finiteEdge _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem finitePick_injective
    (hposition : Function.Injective position) (R : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing)
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ)) :
    Function.Injective (finitePick B D position spacing shift hinside) := by
  intro i j h
  apply pick_injective D position hposition R spacing shift hD hspacing
  have he := congrArg (Target.latticeEdge B) h
  rw [lattice_finitePick, lattice_finitePick] at he
  exact he

omit [Fintype ι] [DecidableEq ι] in
theorem finitePick_support
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ)) (i : ι) (e : B.Edge) :
    0 < Target.defectWeight (blocks B D position spacing shift i) e ↔
      ∃ j, finitePick B D position spacing shift hinside (i, j) = e := by
  rw [blocks, weight_cellBlock, ← ScalarDefect.mem_edges_iff_positive, edges_translate,
    Finset.mem_image]
  constructor
  · rintro ⟨e0, he0, he⟩
    have hrange : e0 ∈ Set.range (ScalarDefect.edgeEmbedding D) := by
      rw [ScalarDefect.range_edgeEmbedding]
      exact he0
    obtain ⟨j, rfl⟩ := hrange
    refine ⟨j, (Target.latticeEdge B).injective ?_⟩
    rw [lattice_finitePick]
    exact he
  · rintro ⟨j, rfl⟩
    refine ⟨ScalarDefect.edgeEmbedding D j, embedding_mem D j, ?_⟩
    rw [lattice_finitePick]
    rfl

/-- Constructed finite layout: disjointness is a theorem of integer placement,
not an additional layout contract. -/
def layout (hposition : Function.Injective position) (R : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing)
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ)) :
    DefectLayout (κ := Fin (ScalarDefect.edges D).card) (blocks B D position spacing shift) where
  pick := finitePick B D position spacing shift hinside
  injective := finitePick_injective B D position spacing shift hposition R hD hspacing hinside
  support := finitePick_support B D position spacing shift hinside

omit [Fintype ι] [DecidableEq ι] in
/-- Every block has the same actual quarter-weight stencil. -/
theorem layout_weight (hposition : Function.Injective position) (R : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing)
    (hinside : ∀ ij k, 0 < (pick D position spacing shift ij).2 k ∧
      (pick D position spacing shift ij).2 k < (Green.boxSide B k : ℤ))
    (ij : ι × Fin (ScalarDefect.edges D).card) :
    (layout B D position spacing shift hposition R hD hspacing hinside).weight ij =
      ScalarDefect.coordinateWeight D ij.2 := by
  change Target.defectWeight (cellBlock B (cells D (anchor position spacing shift ij.1)))
    (finitePick B D position spacing shift hinside ij) = _
  rw [weight_cellBlock, lattice_finitePick]
  exact weight_translate D _ _

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_disjoint (hposition : Function.Injective position) (R : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing) :
    Pairwise (fun i j => Disjoint (blocks B D position spacing shift i)
      (blocks B D position spacing shift j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  exact Finset.disjoint_left.mp
    (cells_disjoint D position hposition R spacing shift hD hspacing hij)
    ((mem_cellBlock _ _ _).mp hci) ((mem_cellBlock _ _ _).mp hcj)

end Layout
end Maxwell.Composition.TranslatedStencil
