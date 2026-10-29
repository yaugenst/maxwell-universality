import Maxwell.Defect.ScalarDefect
import Maxwell.TargetLattice

/-! Exact translated scalar-cell stencils on the actual Yee lattice.
All translated coordinates and quarter weights come from the fixed finite
cell set; disjointness follows from the integer placement and spacing. -/
noncomputable section
namespace Maxwell.Composition.TranslatedStencil
open Maxwell.Spectral
open Maxwell.Spectral.Lattice
open scoped BigOperators

def cells (D : Finset Site) (t : Site) : Finset Site := D.image (fun c => t + c)

def edge (t : Site) (e : Edge) : Edge := (e.1, t + e.2)

theorem edge_injective (t : Site) : Function.Injective (edge t) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have ha := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  simp only [edge, Prod.mk.injEq] at h
  exact Prod.ext ha (add_left_cancel hx)

@[simp] theorem mem_cells (D : Finset Site) (t c : Site) :
    t + c ∈ cells D t ↔ c ∈ D := by
  simp [cells]

@[simp] theorem incidentCell_translate (t : Site) (e : Edge) (j : Fin 4) :
    Maxwell.Defect.ScalarDefect.incidentCell (edge t e) j = t + Maxwell.Defect.ScalarDefect.incidentCell e j := by
  dsimp [edge, Maxwell.Defect.ScalarDefect.incidentCell]
  abel

@[simp] theorem weight_translate (D : Finset Site) (t : Site) (e : Edge) :
    Maxwell.Defect.ScalarDefect.weight (cells D t) (edge t e) = Maxwell.Defect.ScalarDefect.weight D e := by
  unfold Maxwell.Defect.ScalarDefect.weight Maxwell.Defect.ScalarDefect.edgeAverage
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [Maxwell.Defect.ScalarDefect.indicator]

theorem edges_translate (D : Finset Site) (t : Site) :
    Maxwell.Defect.ScalarDefect.edges (cells D t) = (Maxwell.Defect.ScalarDefect.edges D).image (edge t) := by
  ext e
  rw [Maxwell.Defect.ScalarDefect.mem_edges_iff, Finset.mem_image]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp hj
    let e0 : Edge := (e.1, e.2 - t)
    have hmem : e0 ∈ Maxwell.Defect.ScalarDefect.edges D := by
      apply (Maxwell.Defect.ScalarDefect.mem_edges_iff D e0).mpr
      refine ⟨j, ?_⟩
      have heq : Maxwell.Defect.ScalarDefect.incidentCell e0 j = c := by
        dsimp [e0, Maxwell.Defect.ScalarDefect.incidentCell] at hce ⊢
        ext a
        have h := congrFun hce a
        simp only [Pi.add_apply, Pi.sub_apply] at h ⊢
        omega
      rw [heq]
      exact hc
    exact ⟨e0, hmem, by dsimp [e0, edge]; congr 1; abel⟩
  · rintro ⟨e0, he0, rfl⟩
    obtain ⟨j, hj⟩ := (Maxwell.Defect.ScalarDefect.mem_edges_iff D e0).mp he0
    exact ⟨j, by simpa using hj⟩

theorem offset_bounds (a : Direction) (j : Fin 4) (k : Direction) :
    0 ≤ Maxwell.Defect.ScalarDefect.incidentOffset a j k ∧ Maxwell.Defect.ScalarDefect.incidentOffset a j k ≤ 1 := by
  fin_cases a <;> fin_cases j <;> fin_cases k <;>
    norm_num [Maxwell.Defect.ScalarDefect.incidentOffset, PeriodicYee.transverseDirections, unitSite]

/-- A touched edge differs from one of its actual incident defect cells by
at most one in every coordinate. -/
theorem edge_bounds (D : Finset Site) (R : ℕ)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (e : Edge) (he : e ∈ Maxwell.Defect.ScalarDefect.edges D) (k : Direction) :
    -(R : ℤ) ≤ e.2 k ∧ e.2 k ≤ (R : ℤ) + 1 := by
  obtain ⟨j, hj⟩ := (Maxwell.Defect.ScalarDefect.mem_edges_iff D e).mp he
  have hc := hD (Maxwell.Defect.ScalarDefect.incidentCell e j) hj k
  have ho := offset_bounds e.1 j k
  simp only [Maxwell.Defect.ScalarDefect.incidentCell, Pi.sub_apply] at hc
  omega

def anchor {ι : Type*} (position : ι → Site) (spacing : ℕ) (shift : Site) (i : ι) : Site :=
  shift + (spacing : ℤ) • position i

def pick {ι : Type*} (D : Finset Site) (position : ι → Site) (spacing : ℕ) (shift : Site) :
    ι × Fin (Maxwell.Defect.ScalarDefect.edges D).card → Edge :=
  fun ij => edge (anchor position spacing shift ij.1) (Maxwell.Defect.ScalarDefect.edgeEmbedding D ij.2)

theorem embedding_mem (D : Finset Site) (j : Fin (Maxwell.Defect.ScalarDefect.edges D).card) :
    Maxwell.Defect.ScalarDefect.edgeEmbedding D j ∈ Maxwell.Defect.ScalarDefect.edges D := by
  change Maxwell.Defect.ScalarDefect.edgeEmbedding D j ∈ (Maxwell.Defect.ScalarDefect.edges D : Set Edge)
  rw [← Maxwell.Defect.ScalarDefect.range_edgeEmbedding]
  exact ⟨j, rfl⟩

theorem integer_spacing_unique (B R x y a b : ℤ)
    (hB : 2 * (R + 1) < B) (ha : -R ≤ a ∧ a ≤ R + 1)
    (hb : -R ≤ b ∧ b ≤ R + 1) (he : B * x + a = B * y + b) : x = y := by
  have hB0 : 0 < B := by
    have hR : -R ≤ R + 1 := ha.1.trans ha.2
    omega
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hstep : x + 1 ≤ y := by omega
    have hm := mul_le_mul_of_nonneg_left hstep hB0.le
    nlinarith
  · have hstep : y + 1 ≤ x := by omega
    have hm := mul_le_mul_of_nonneg_left hstep hB0.le
    nlinarith

/-- Integer lattice separation gives injectivity of the whole union of
translated touched-edge stencils, including distinct blocks. -/
theorem pick_injective {ι : Type*} (D : Finset Site) (position : ι → Site)
    (hposition : Function.Injective position) (R spacing : ℕ) (shift : Site)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing) :
    Function.Injective (pick D position spacing shift) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hij : i = j := by
    apply hposition
    funext k
    have h := congrArg (fun e : Edge => e.2 k) he
    have ha := edge_bounds D R hD _ (embedding_mem D a) k
    have hb := edge_bounds D R hD _ (embedding_mem D b) k
    dsimp [pick, edge, anchor] at h
    exact integer_spacing_unique spacing R (position i k) (position j k)
      ((Maxwell.Defect.ScalarDefect.edgeEmbedding D a).2 k) ((Maxwell.Defect.ScalarDefect.edgeEmbedding D b).2 k)
      (by exact_mod_cast hspacing) ha hb (by linarith)
  subst j
  have hab : a = b := (Maxwell.Defect.ScalarDefect.edgeEmbedding D).injective ((edge_injective _ ) he)
  exact Prod.ext rfl hab

theorem cells_disjoint {ι : Type*} (D : Finset Site) (position : ι → Site)
    (hposition : Function.Injective position) (R spacing : ℕ) (shift : Site)
    (hD : ∀ c ∈ D, ∀ k, -(R : ℤ) ≤ c k ∧ c k ≤ R)
    (hspacing : 2 * (R + 1) < spacing) {i j : ι} (hij : i ≠ j) :
    Disjoint (cells D (anchor position spacing shift i))
      (cells D (anchor position spacing shift j)) := by
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hci
  obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hcj
  apply hij
  apply hposition
  funext k
  have he := congrFun (hac.trans hbc.symm) k
  dsimp [anchor] at he
  exact integer_spacing_unique spacing R (position i k) (position j k) (a k) (b k)
    (by exact_mod_cast hspacing) ⟨(hD a ha k).1, by linarith [(hD a ha k).2]⟩
    ⟨(hD b hb k).1, by linarith [(hD b hb k).2]⟩ (by linarith)

/-- The finite PEC interface enumerates the same four cells in reverse order. -/
theorem incidentCell_order (e : Edge) (j : Fin 4) :
    Target.latticeIncidentCells e j =
      Maxwell.Defect.ScalarDefect.incidentCell e j.rev := by
  rcases e with ⟨a, x⟩
  fin_cases a <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [Target.latticeIncidentCells, Maxwell.Defect.ScalarDefect.incidentCell,
      Maxwell.Defect.ScalarDefect.incidentOffset, PeriodicYee.transverseDirections, unitSite]

end Maxwell.Composition.TranslatedStencil
