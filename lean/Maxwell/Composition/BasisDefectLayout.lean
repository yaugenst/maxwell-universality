import Maxwell.Composition.SourceDefectBounds

/-! The certified integer change of lattice basis is applied to the actual
routed vertices before placing physical defect stencils. Finite-box margins
and volume are derived from a fixed, computable coefficient bound. -/
noncomputable section
namespace Maxwell.Composition.BasisDefectLayout
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil
open scoped BigOperators

def coefficientSize (B : Matrix Direction Direction ℤ) : ℕ :=
  ∑ i, ∑ j, (B i j).natAbs

def extent (base : Target.Box) (B : Matrix Direction Direction ℤ) : ℕ :=
  coefficientSize B * (base.nx + base.ny + base.nz)

def transformedBox (base : Target.Box) (B : Matrix Direction Direction ℤ) : Target.Box :=
  ⟨2 * extent base B + 1, 2 * extent base B + 1, 2 * extent base B + 1⟩

def transformedPosition (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (c : base.Cell) : Site := fun i => B.mulVec (Target.latticeCell c) i + (extent base B : ℕ)

theorem coefficient_le (B : Matrix Direction Direction ℤ) (i j : Direction) :
    (B i j).natAbs ≤ coefficientSize B := by
  have hj : (B i j).natAbs ≤ ∑ k, (B i k).natAbs :=
    Finset.single_le_sum (f := fun k : Direction => (B i k).natAbs)
      (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi : (∑ k, (B i k).natAbs) ≤ ∑ a, ∑ k, (B a k).natAbs :=
    Finset.single_le_sum (f := fun a : Direction => ∑ k : Direction, (B a k).natAbs)
      (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hj.trans hi

theorem transformed_bounds (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (c : base.Cell) (i : Direction) :
    -(extent base B : ℤ) ≤ B.mulVec (Target.latticeCell c) i ∧
      B.mulVec (Target.latticeCell c) i ≤ extent base B := by
  have hcell : ∀ j, |Target.latticeCell c j| ≤ (base.nx + base.ny + base.nz : ℕ) := by
    intro j
    have h := latticeCell_bounds base c j
    rw [abs_of_nonneg h.1]
    fin_cases j <;> dsimp [Green.boxSide, Target.latticeCell] at h ⊢ <;> omega
  have hrow : ∑ j, |B i j| ≤ (coefficientSize B : ℤ) := by
    have hnat : (∑ j, (B i j).natAbs) ≤ ∑ a, ∑ j, (B a j).natAbs :=
      Finset.single_le_sum (f := fun a : Direction => ∑ k : Direction, (B a k).natAbs)
      (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
    have hcast := (show ((∑ j, (B i j).natAbs : ℕ) : ℤ) ≤
      ((∑ a, ∑ j, (B a j).natAbs : ℕ) : ℤ) from by exact_mod_cast hnat)
    simpa only [Nat.cast_sum, Int.natCast_natAbs, coefficientSize] using hcast
  have habs : |B.mulVec (Target.latticeCell c) i| ≤ (extent base B : ℤ) := by
    calc
      _ ≤ ∑ j, |B i j * Target.latticeCell c j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |B i j| * |Target.latticeCell c j| := by simp only [abs_mul]
      _ ≤ ∑ j, |B i j| * (base.nx + base.ny + base.nz : ℕ) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcell j) (abs_nonneg _)
      _ = (∑ j, |B i j|) * (base.nx + base.ny + base.nz : ℕ) := (Finset.sum_mul _ _ _).symm
      _ ≤ (coefficientSize B : ℤ) * (base.nx + base.ny + base.nz : ℕ) :=
        mul_le_mul_of_nonneg_right hrow (by positivity)
      _ = _ := by simp only [extent, Nat.cast_mul]
  exact abs_le.mp habs

theorem transformed_inside (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (c : base.Cell) (i : Direction) :
    0 ≤ transformedPosition base B c i ∧
      transformedPosition base B c i < (Green.boxSide (transformedBox base B) i : ℤ) := by
  have h := transformed_bounds base B c i
  have hs : Green.boxSide (transformedBox base B) i = 2 * extent base B + 1 := by
    fin_cases i <;> rfl
  rw [hs]
  dsimp [transformedPosition]
  omega

/-- Direct integer matrix-vector multiplication followed by finite-cell indexing. -/
def transformedIndex (base : Target.Box) (B : Matrix Direction Direction ℤ) (c : base.Cell) :
    (transformedBox base B).Cell := finiteCell _ _ (transformed_inside base B c)

@[simp] theorem transformedIndex_lattice (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (c : base.Cell) : Target.latticeCell (transformedIndex base B c) = transformedPosition base B c :=
  lattice_finiteCell _ _ _

theorem transformedIndex_injective (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (hB : Function.Injective B.mulVec) : Function.Injective (transformedIndex base B) := by
  intro c d he
  have h := congrArg Target.latticeCell he
  rw [transformedIndex_lattice, transformedIndex_lattice] at h
  apply latticeCell_injective base
  apply hB
  funext i
  exact add_right_cancel (congrFun h i)

theorem transformedPosition_sub (base : Target.Box) (B : Matrix Direction Direction ℤ)
    (c d : base.Cell) : transformedPosition base B c - transformedPosition base B d =
      B.mulVec (Target.latticeCell c - Target.latticeCell d) := by
  rw [Matrix.mulVec_sub]
  ext i
  dsimp [transformedPosition]
  abel

section Source
variable (S : Source.SparseSystem) (precision : ℕ) (B : Matrix Direction Direction ℤ)

def baseBox : Target.Box := transformedBox (SourceDefectLayout.baseBox S precision) B

def indices : SourceRouting.Vertex S precision → (baseBox S precision B).Cell :=
  fun i => transformedIndex _ B (SourceDefectLayout.indices S precision i)

theorem indices_injective (hB : Function.Injective B.mulVec) :
    Function.Injective (indices S precision B) :=
  (transformedIndex_injective _ B hB).comp (SourceDefectLayout.indices_injective _ _)

def position : SourceRouting.Vertex S precision → Site :=
  fun i => Target.latticeCell (indices S precision B i)

def physicalBox (D : Finset Site) (macroSpacing buffer : ℕ) : Target.Box :=
  bufferedBox (baseBox S precision B) (SourceDefectLayout.radius D) (20 * macroSpacing) buffer

def conventionalAnchor (D : Finset Site) (macroSpacing buffer : ℕ)
    (i : SourceRouting.Vertex S precision) : Site :=
  (fun _ : Direction => ((SourceDefectLayout.radius D + buffer + 1 : ℕ) : ℤ)) +
    (macroSpacing : ℤ) • position S precision B i

theorem anchor_period (D : Finset Site) (macroSpacing buffer : ℕ)
    (i : SourceRouting.Vertex S precision) :
    anchor (position S precision B) (20 * macroSpacing)
      (bufferedShift (SourceDefectLayout.radius D) buffer) i =
      (20 : ℤ) • conventionalAnchor S precision B D macroSpacing buffer i := by
  ext k
  simp [anchor, bufferedShift, conventionalAnchor]
  ring

/-- The block separation is exactly the certified integer basis applied to
the actual routed lattice displacement, including its orientation. -/
theorem anchor_difference (D : Finset Site) (macroSpacing buffer : ℕ)
    (i j : SourceRouting.Vertex S precision) :
    conventionalAnchor S precision B D macroSpacing buffer i -
      conventionalAnchor S precision B D macroSpacing buffer j =
      (macroSpacing : ℤ) • B.mulVec
        (SourceDefectLayout.position S precision i - SourceDefectLayout.position S precision j) := by
  have h : position S precision B i - position S precision B j =
      B.mulVec (SourceDefectLayout.position S precision i - SourceDefectLayout.position S precision j) := by
    change Target.latticeCell (transformedIndex _ B (SourceDefectLayout.indices S precision i)) -
      Target.latticeCell (transformedIndex _ B (SourceDefectLayout.indices S precision j)) = _
    rw [transformedIndex_lattice, transformedIndex_lattice]
    exact transformedPosition_sub _ B _ _
  rw [← h, smul_sub]
  simp only [conventionalAnchor]
  abel

def cellBlocks (D : Finset Site) (macroSpacing buffer : ℕ) :
    SourceRouting.Vertex S precision → Finset (physicalBox S precision B D macroSpacing buffer).Cell :=
  blocks (physicalBox S precision B D macroSpacing buffer) D (position S precision B)
    (20 * macroSpacing) (bufferedShift (SourceDefectLayout.radius D) buffer)

theorem inside (D : Finset Site) (macroSpacing buffer : ℕ)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) (k : Direction) :
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
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) :
    (layout S precision B hB D macroSpacing buffer hspacing).weight ij =
      ScalarDefect.coordinateWeight D ij.2 := by
  classical
  exact layout_weight _ D (position S precision B) (20 * macroSpacing)
    (bufferedShift (SourceDefectLayout.radius D) buffer)
    ((latticeCell_injective _).comp (indices_injective S precision B hB))
    _ (SourceDefectLayout.radius_bounds D) hspacing (inside S precision B D macroSpacing buffer) ij

theorem lattice_pick (hB : Function.Injective B.mulVec) (D : Finset Site) (macroSpacing buffer : ℕ)
    (hspacing : 2 * (SourceDefectLayout.radius D + 1) < 20 * macroSpacing)
    (ij : SourceRouting.Vertex S precision × Fin (ScalarDefect.edges D).card) :
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
end Maxwell.Composition.BasisDefectLayout
