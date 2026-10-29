import Maxwell.Continuum.CellSpatialLocalization
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! The literal period-two spatial cells form a disjoint measurable
tiling. A finite, explicitly counted set covers each radius-L ball. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open CellBandFourier Bloch MeasureTheory Set

def cellIndex (x : Space) : Bloch.Alias := fun j => ⌈x j / 2⌉ - 1

theorem spatialBox_mem (a : Bloch.Alias) (x : Space) :
    x ∈ spatialBox a ↔ ∀ j, 2 * (a j : ℝ) < x j ∧ x j ≤ 2 * (a j : ℝ) + 2 := by
  rw [spatialBox, mem_ofPred_eq, physicalCell_mem]
  simp only [PiLp.sub_apply, latticeShift, PiLp.smul_apply, integerVector_apply, smul_eq_mul]
  constructor <;> intro hx j <;> have hj := hx j <;> constructor <;> linarith

theorem spatialBox_iff_index (a : Bloch.Alias) (x : Space) :
    x ∈ spatialBox a ↔ cellIndex x = a := by
  rw [spatialBox_mem]
  constructor
  · intro hx
    funext j
    have hc : ⌈x j / 2⌉ = a j + 1 := by
      apply Int.ceil_eq_iff.mpr
      push_cast
      exact ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩
    simp only [cellIndex, hc, add_sub_cancel_right]
  · intro hx j
    have hc : ⌈x j / 2⌉ = a j + 1 := by
      have hj := congrFun hx j
      change ⌈x j / 2⌉ - 1 = a j at hj
      omega
    have hp := Int.ceil_eq_iff.mp hc
    push_cast at hp
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

theorem mem_spatialBox_index (x : Space) : x ∈ spatialBox (cellIndex x) :=
  (spatialBox_iff_index _ _).mpr rfl

theorem spatialBox_disjoint {a b : Bloch.Alias} (hab : a ≠ b) :
    Disjoint (spatialBox a) (spatialBox b) := by
  rw [Set.disjoint_left]
  intro x ha hb
  exact hab (((spatialBox_iff_index a x).mp ha).symm.trans ((spatialBox_iff_index b x).mp hb))

def ballCellRadius (L : ℝ) : ℕ := ⌈L⌉₊ + 2

def ballCells (L : ℝ) : Finset Bloch.Alias :=
  Fintype.piFinset (fun _ : Fin 3 =>
    Finset.Icc (-(ballCellRadius L : ℤ)) (ballCellRadius L : ℤ))

theorem cellIndex_mem_ballCells {L : ℝ} {x : Space} (hx : ‖x‖ ≤ L) :
    cellIndex x ∈ ballCells L := by
  apply Fintype.mem_piFinset.mpr
  intro j
  rw [Finset.mem_Icc]
  have hnorm₀ : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  have hnorm : |x j| ≤ L := hnorm₀.trans hx
  have hl := Nat.le_ceil L
  have hc₁ := Int.le_ceil (x j / 2)
  have hc₂ := Int.ceil_lt_add_one (x j / 2)
  have hlow : -(ballCellRadius L : ℝ) ≤ (cellIndex x j : ℝ) := by
    simp only [ballCellRadius, Nat.cast_add, Nat.cast_ofNat, cellIndex, Int.cast_sub, Int.cast_one]
    linarith [(abs_le.mp hnorm).1]
  have hupp : (cellIndex x j : ℝ) ≤ (ballCellRadius L : ℝ) := by
    simp only [ballCellRadius, Nat.cast_add, Nat.cast_ofNat, cellIndex, Int.cast_sub, Int.cast_one]
    linarith [(abs_le.mp hnorm).2]
  exact ⟨by exact_mod_cast hlow, by exact_mod_cast hupp⟩

theorem ballCells_card (L : ℝ) : (ballCells L).card = (2 * ballCellRadius L + 1)^3 := by
  rw [ballCells, Fintype.card_piFinset_const]
  congr 1
  rw [Int.card_Icc]
  omega

theorem ballCells_card_le {L : ℝ} (hL : 1 ≤ L) :
    ((ballCells L).card : ℝ) ≤ (2 : ℝ)^10 * L^3 := by
  rw [ballCells_card]
  push_cast
  have hc := Nat.ceil_lt_add_one (show 0 ≤ L by linarith)
  have hN : (ballCellRadius L : ℝ) ≤ L + 3 := by
    simp only [ballCellRadius, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hb : 2 * (ballCellRadius L : ℝ) + 1 ≤ 9 * L := by linarith
  calc
    _ ≤ (9 * L)^3 := pow_le_pow_left₀ (by positivity) hb 3
    _ ≤ (2 : ℝ)^10 * L^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ L) 3]

#print axioms spatialBox_iff_index
#print axioms ballCells_card_le

end Maxwell.Continuum.CellGauge
