import Maxwell.Composition.FiniteDefectLayout

/-! Explicit buffered PEC boxes for finite integer placements. -/
noncomputable section
namespace Maxwell.Composition.TranslatedStencil
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open scoped BigOperators

theorem latticeCell_injective (B : Target.Box) :
    Function.Injective (@Target.latticeCell B) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [Target.latticeCell] at h0 h1 h2
  exact Prod.ext (Fin.ext (by exact_mod_cast h0))
    (Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2)))

theorem latticeCell_bounds (B : Target.Box) (c : B.Cell) (k : Direction) :
    0 ≤ Target.latticeCell c k ∧ Target.latticeCell c k < (Green.boxSide B k : ℤ) := by
  have h0 := c.1.isLt
  have h1 := c.2.1.isLt
  have h2 := c.2.2.isLt
  fin_cases k <;> dsimp [Target.latticeCell, Green.boxSide] <;> omega

/-- Direct scalar-cell insertion, with no search or choice of a representative. -/
def finiteCell (B : Target.Box) (c : Site)
    (hc : ∀ k, 0 ≤ c k ∧ c k < (Green.boxSide B k : ℤ)) : B.Cell :=
  (⟨(c 0).toNat, by have h := hc 0; simp [Green.boxSide] at h; omega⟩,
   ⟨(c 1).toNat, by have h := hc 1; simp [Green.boxSide] at h; omega⟩,
   ⟨(c 2).toNat, by have h := hc 2; simp [Green.boxSide] at h; omega⟩)

@[simp] theorem lattice_finiteCell (B : Target.Box) (c : Site)
    (hc : ∀ k, 0 ≤ c k ∧ c k < (Green.boxSide B k : ℤ)) :
    Target.latticeCell (finiteCell B c hc) = c := by
  ext k
  have h0 := (hc 0).1
  have h1 := (hc 1).1
  have h2 := (hc 2).1
  fin_cases k <;> simp [finiteCell, Target.latticeCell] <;> omega

theorem cellBlock_image (B : Target.Box) (D : Finset Site)
    (hD : ∀ c ∈ D, ∀ k, 0 ≤ c k ∧ c k < (Green.boxSide B k : ℤ)) :
    (cellBlock B D).image Target.latticeCell = D := by
  ext c
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact (mem_cellBlock _ _ _).mp ha
  · intro hc
    refine Finset.mem_image.mpr ⟨finiteCell B c (hD c hc), ?_, lattice_finiteCell _ _ _⟩
    simp [hc]

def bufferedBox (base : Target.Box) (R spacing buffer : ℕ) : Target.Box where
  nx := spacing * base.nx + 40 * (R + buffer + 2)
  ny := spacing * base.ny + 40 * (R + buffer + 2)
  nz := spacing * base.nz + 40 * (R + buffer + 2)

def bufferedShift (R buffer : ℕ) : Site := fun _ => (20 * (R + buffer + 1) : ℕ)

@[simp] theorem bufferedBox_side (base : Target.Box) (R spacing buffer : ℕ) (k : Direction) :
    Green.boxSide (bufferedBox base R spacing buffer) k =
      spacing * Green.boxSide base k + 40 * (R + buffer + 2) := by
  fin_cases k <;> rfl

/-- The prototype cell support may be asymmetric; a single coordinate radius
is enough for its exact placed cell set and touched-edge union. -/
theorem buffered_pick_margin {ι : Type*} (base : Target.Box) (indices : ι → base.Cell)
    (D : Finset Site) (R spacing buffer : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (ij : ι × Fin (ScalarDefect.edges D).card) (k : Direction) :
    (buffer : ℤ) + 1 ≤
        (pick D (fun i => Target.latticeCell (indices i)) spacing (bufferedShift R buffer) ij).2 k ∧
      (pick D (fun i => Target.latticeCell (indices i)) spacing (bufferedShift R buffer) ij).2 k +
        ((buffer : ℤ) + 1) ≤ (Green.boxSide (bufferedBox base R spacing buffer) k : ℤ) := by
  have hp := latticeCell_bounds base (indices ij.1) k
  have he := edge_bounds D R hD _ (embedding_mem D ij.2) k
  have hmul0 : 0 ≤ (spacing : ℤ) * Target.latticeCell (indices ij.1) k := mul_nonneg (by positivity) hp.1
  have hmul := mul_le_mul_of_nonneg_left hp.2.le (by positivity : (0 : ℤ) ≤ spacing)
  simp only [pick, edge, anchor, bufferedShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    bufferedBox_side, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  constructor <;> omega

theorem buffered_pick_inside {ι : Type*} (base : Target.Box) (indices : ι → base.Cell)
    (D : Finset Site) (R spacing buffer : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (ij : ι × Fin (ScalarDefect.edges D).card) (k : Direction) :
    0 < (pick D (fun i => Target.latticeCell (indices i)) spacing (bufferedShift R buffer) ij).2 k ∧
      (pick D (fun i => Target.latticeCell (indices i)) spacing (bufferedShift R buffer) ij).2 k <
        (Green.boxSide (bufferedBox base R spacing buffer) k : ℤ) := by
  have h := buffered_pick_margin base indices D R spacing buffer hD ij k
  omega

theorem buffered_cells_inside {ι : Type*} (base : Target.Box) (indices : ι → base.Cell)
    (D : Finset Site) (R spacing buffer : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (i : ι) (c : Site)
    (hc : c ∈ cells D (anchor (fun i => Target.latticeCell (indices i)) spacing
      (bufferedShift R buffer) i)) (k : Direction) :
    0 ≤ c k ∧ c k < (Green.boxSide (bufferedBox base R spacing buffer) k : ℤ) := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
  have hp := latticeCell_bounds base (indices i) k
  have he := hD a ha k
  have hmul0 : 0 ≤ (spacing : ℤ) * Target.latticeCell (indices i) k := mul_nonneg (by positivity) hp.1
  have hmul := mul_le_mul_of_nonneg_left hp.2.le (by positivity : (0 : ℤ) ≤ spacing)
  simp only [anchor, bufferedShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    bufferedBox_side, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  constructor <;> omega

/-- Complete geometric layout from the finite placement table. The box and
all selected PEC indices are explicitly constructed. -/
def bufferedLayout {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : Target.Box) (indices : ι → base.Cell) (hinj : Function.Injective indices)
    (D : Finset Site) (R spacing buffer : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing) :=
  layout (bufferedBox base R spacing buffer) D (fun i => Target.latticeCell (indices i))
    spacing (bufferedShift R buffer) ((latticeCell_injective base).comp hinj) R hD hspacing
    (buffered_pick_inside base indices D R spacing buffer hD)

end Maxwell.Composition.TranslatedStencil
