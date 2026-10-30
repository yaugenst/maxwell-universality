import Maxwell.Continuum.CellDistance

/-! Explicit finite cell families for an even-sided physical box.
Two outer cell layers are separated from buffered source cells by the
literal Euclidean cell distance used in the resolvent estimates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open CellGauge Bloch

def side (n : Fin 3 → ℕ) (j : Fin 3) : ℝ := 2*(n j : ℝ)

def cells (n : Fin 3 → ℕ) : Finset Alias :=
  Fintype.piFinset fun j => Finset.Icc (0 : ℤ) ((n j : ℤ)-1)

def boundaryCells (n : Fin 3 → ℕ) : Finset Alias := by
  classical
  exact (cells n).filter fun a => ∃ j, a j ≤ 1 ∨ (n j : ℤ)-2 ≤ a j

def interiorCells (n : Fin 3 → ℕ) (b : ℝ) : Finset Alias := by
  classical
  exact (cells n).filter fun a => ∀ j,
    b+4 ≤ 2*(a j : ℝ) ∧ 2*(a j : ℝ)+2 ≤ side n j-b-4

theorem cells_card (n : Fin 3 → ℕ) : (cells n).card = ∏ j, n j := by
  rw [cells, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  rw [Int.card_Icc]
  omega

theorem boundaryCells_card (n : Fin 3 → ℕ) : (boundaryCells n).card ≤ ∏ j, n j := by
  classical
  rw [← cells_card]
  exact Finset.card_filter_le _ _

theorem interiorCells_card (n : Fin 3 → ℕ) (b : ℝ) : (interiorCells n b).card ≤ ∏ j, n j := by
  classical
  rw [← cells_card]
  exact Finset.card_filter_le _ _

theorem index_mem_cells (n : Fin 3 → ℕ) {x : Space}
    (hx : ∀ j, 0 < x j ∧ x j ≤ side n j) : cellIndex x ∈ cells n := by
  apply Fintype.mem_piFinset.mpr
  intro j
  rw [Finset.mem_Icc]
  have ha := (spatialBox_mem _ _).mp (mem_spatialBox_index x) j
  have hn := hx j
  dsimp only [side] at hn
  have hlow : (-1 : ℝ) < (cellIndex x j : ℝ) := by linarith only [ha.2, hn.1]
  have hupp : (cellIndex x j : ℝ) < (n j : ℝ) := by linarith only [ha.1, hn.2]
  have hlow' : (-1 : ℤ) < cellIndex x j := by exact_mod_cast hlow
  have hupp' : cellIndex x j < (n j : ℤ) := by exact_mod_cast hupp
  omega

theorem index_mem_interiorCells (n : Fin 3 → ℕ) {b : ℝ} (hb : 0 ≤ b) {x : Space}
    (hx : ∀ j, b+6 ≤ x j ∧ x j ≤ side n j-b-6) : cellIndex x ∈ interiorCells n b := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨index_mem_cells n (fun j => ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩), ?_⟩
  intro j
  have ha := (spatialBox_mem _ _).mp (mem_spatialBox_index x) j
  exact ⟨by linarith [ha.2, (hx j).1], by linarith [ha.1, (hx j).2]⟩

theorem buffered_cell_distance (n : Fin 3 → ℕ) (b : ℝ) {a c : Alias}
    (ha : a ∈ boundaryCells n) (hc : c ∈ interiorCells n b) : b ≤ paperCellDistance a c := by
  classical
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp ha).2
  have hcj := (Finset.mem_filter.mp hc).2 j
  unfold paperCellDistance
  have hS : ({r : Space | ∃ x ∈ paperBox a, ∃ y ∈ paperBox c, r = x-y} : Set Space).Nonempty :=
    ⟨latticeShift a-latticeShift c,
    latticeShift a, latticeShift_mem_paperBox a,
    latticeShift c, latticeShift_mem_paperBox c, rfl⟩
  apply (Metric.le_infDist (x := (0 : Space)) hS).mpr
  rintro r ⟨x, hx, y, hy, rfl⟩
  rw [dist_zero_left]
  have hnorm : |x j-y j| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) j
  have hxj := hx j
  have hyj := hy j
  rcases hj with hj | hj
  · have hjr : (a j : ℝ) ≤ 1 := by exact_mod_cast hj
    apply le_trans _ hnorm
    exact (by linarith only [hcj.1, hxj.2, hyj.1, hjr] : b ≤ -(x j-y j)).trans (neg_le_abs _)
  · have hjr : (n j : ℝ)-2 ≤ (a j : ℝ) := by exact_mod_cast hj
    dsimp only [side] at hcj
    apply le_trans _ hnorm
    exact (by linarith only [hcj.2, hxj.1, hyj.2, hjr] : b ≤ x j-y j).trans (le_abs_self _)

#print axioms buffered_cell_distance

end Maxwell.Continuum.BoxCutoff
