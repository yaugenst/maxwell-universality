import Maxwell.TargetGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field

namespace Maxwell.Target

open scoped BigOperators

def defectIndicator {B : Box} (D : Finset B.Cell) (c : B.Cell) : ℚ :=
  if c ∈ D then 1 else 0

def defectWeight {B : Box} (D : Finset B.Cell) (e : B.Edge) : ℚ :=
  edgeAverage (defectIndicator D) e

def defectHits {B : Box} (D : Finset B.Cell) (e : B.Edge) : Finset (Fin 4) :=
  Finset.univ.filter fun j => incidentCells e j ∈ D

/-- The physical edge weight is precisely the fraction of incident cells
belonging to the scalar defect, including at the PEC boundary. -/
theorem defectWeight_eq_count {B : Box} (D : Finset B.Cell) (e : B.Edge) :
    defectWeight D e = (defectHits D e).card / 4 := by
  have hc : ((defectHits D e).card : ℚ) =
      ∑ j : Fin 4, if incidentCells e j ∈ D then (1 : ℚ) else 0 := by
    rw [defectHits, Finset.card_filter]
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> norm_num
  rw [hc]
  simp only [defectWeight, edgeAverage, defectIndicator, Fin.sum_univ_four]

theorem defectWeight_bounds {B : Box} (D : Finset B.Cell) (e : B.Edge) :
    0 ≤ defectWeight D e ∧ defectWeight D e ≤ 1 := by
  have hc : (defectHits D e).card ≤ 4 := by
    simpa only [defectHits, Finset.card_univ, Fintype.card_fin] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin 4)))
      (p := fun j => incidentCells e j ∈ D)
  rw [defectWeight_eq_count]
  constructor
  · positivity
  · have hc' : ((defectHits D e).card : ℚ) ≤ 4 := by exact_mod_cast hc
    linarith

theorem defectWeight_positive_iff {B : Box} (D : Finset B.Cell) (e : B.Edge) :
    0 < defectWeight D e ↔ ∃ j, incidentCells e j ∈ D := by
  rw [defectWeight_eq_count, div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 4)]
  rw [Nat.cast_pos, Finset.card_pos]
  simp [defectHits, Finset.Nonempty]

/-- No positive edge weight is arbitrarily small: the four-cell convention
gives the exact dimension-independent lower bound one quarter. -/
theorem defectWeight_quarter_le {B : Box} (D : Finset B.Cell) (e : B.Edge)
    (h : 0 < defectWeight D e) : 1 / 4 ≤ defectWeight D e := by
  have hc : 0 < (defectHits D e).card := by
    rw [defectWeight_eq_count] at h
    exact_mod_cast ((div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 4)).mp h)
  have hc' : (1 : ℚ) ≤ (defectHits D e).card := by exact_mod_cast hc
  rw [defectWeight_eq_count]
  linarith

theorem edgeAverage_add {B : Box} (a b : B.Cell → ℚ) (e : B.Edge) :
    edgeAverage (fun c => a c + b c) e = edgeAverage a e + edgeAverage b e := by
  dsimp [edgeAverage]
  ring

theorem edgeAverage_mul {B : Box} (z : ℚ) (a : B.Cell → ℚ) (e : B.Edge) :
    edgeAverage (fun c => z * a c) e = z * edgeAverage a e := by
  dsimp [edgeAverage]
  ring

theorem edgeAverage_sum {B : Box} {ι : Type*} [Fintype ι]
    (a : ι → B.Cell → ℚ) (e : B.Edge) :
    edgeAverage (fun c => ∑ i, a i c) e = ∑ i, edgeAverage (a i) e := by
  simp only [edgeAverage]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib]

/-- Exact scalar-cell encoding of all local defect strengths. -/
def assembledMaterial {B : Box} {ι : Type*} [Fintype ι]
    (background : B.Cell → ℚ) (blocks : ι → Finset B.Cell) (v : ι → ℚ)
    (c : B.Cell) : ℚ :=
  background c + 64 * ∑ i, v i * defectIndicator (blocks i) c

theorem assembledMaterial_edgeAverage {B : Box} {ι : Type*} [Fintype ι]
    (background : B.Cell → ℚ) (blocks : ι → Finset B.Cell) (v : ι → ℚ)
    (e : B.Edge) :
    edgeAverage (assembledMaterial background blocks v) e =
      edgeAverage background e + 64 * ∑ i, v i * defectWeight (blocks i) e := by
  unfold assembledMaterial
  rw [edgeAverage_add, edgeAverage_mul, edgeAverage_sum]
  simp only [edgeAverage_mul, defectWeight]

/-- The emitted scalar cells induce the claimed complete Maxwell operator.
The curl, all auxiliary edges and every untouched cell remain accounted for. -/
theorem assembledMaterial_operator {B : Box} {ι : Type*} [Fintype ι]
    (background : B.Cell → ℚ) (blocks : ι → Finset B.Cell) (v : ι → ℚ) :
    operator B (assembledMaterial background blocks v) = operator B background -
      Matrix.diagonal (fun e => ∑ i, v i * defectWeight (blocks i) e) := by
  ext e f
  by_cases h : e = f
  · subst f
    simp [operator, assembledMaterial_edgeAverage]
    ring
  · simp [operator, h]

/-- Disjoint cell supports prevent accumulation of defect strengths at any
cell. This is an exact sum identity rather than a cardinality bound. -/
theorem disjoint_defect_cell_sum {B : Box} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blocks : ι → Finset B.Cell) (v : ι → ℚ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (c : B.Cell) (i : ι) (hi : c ∈ blocks i) :
    (∑ j, v j * defectIndicator (blocks j) c) = v i := by
  rw [Finset.sum_eq_single i]
  · simp [defectIndicator, hi]
  · intro j _ hji
    have hj : c ∉ blocks j := by
      intro hj
      exact Finset.disjoint_left.mp (hdisj j i hji) hj hi
    simp [defectIndicator, hj]
  · simp

/-- Every physical cell stays admissible on every draw once the emitted
individual strengths respect the reserved material interval. -/
theorem assembledMaterial_bounds {B : Box} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (background : B.Cell → ℚ) (blocks : ι → Finset B.Cell) (v : ι → ℚ)
    (headroom : ℚ) (hh : 0 ≤ headroom)
    (hbase : ∀ c, 1 ≤ background c ∧ background c ≤ 25 - headroom)
    (hv : ∀ i, 0 ≤ v i ∧ 64 * v i ≤ headroom)
    (hdisj : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (c : B.Cell) :
    1 ≤ assembledMaterial background blocks v c ∧
      assembledMaterial background blocks v c ≤ 25 := by
  classical
  unfold assembledMaterial
  by_cases h : ∃ i, c ∈ blocks i
  · obtain ⟨i, hi⟩ := h
    rw [disjoint_defect_cell_sum blocks v hdisj c i hi]
    have hb := hbase c
    have ht := hv i
    constructor <;> linarith
  · have hz : ∀ i, c ∉ blocks i := by simpa using h
    simp only [defectIndicator, ite_eq_right (hz _), mul_zero, Finset.sum_const_zero, add_zero]
    have hb := hbase c
    constructor <;> linarith

end Maxwell.Target
