import Maxwell.Composition.PhysicalBackground

/-! A rational, certified Combes--Thomas exponent and an actual buffer
choice for the complete decorated PEC box. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice
open Maxwell.Composition.BasisDefectLayout Maxwell.Composition.TranslatedStencil

private theorem rational_combes_small (g : ℝ) (hg : 0 < g) :
    16 * (Real.exp (2 * (g / (128 + 2*g))) - 1) ≤ g / 4 := by
  let μ := g / (128 + 2*g)
  have hμ : 0 < μ := div_pos hg (by positivity)
  have hμ2 : μ < 1/2 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  have heq : μ * (128 + 2*g) = g := by dsimp [μ]; field_simp
  have he := Real.exp_le_two_add_div_two_sub (by positivity : 0 ≤ 2*μ)
    (by linarith : 2*μ < 2)
  have hr : (2 + 2*μ) / (2 - 2*μ) ≤ 1 + g/64 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 - 2*μ)).mpr
    nlinarith [mul_nonneg hμ.le hg.le]
  change 16 * (Real.exp (2*μ) - 1) ≤ g/4
  linarith

namespace PhysicalPlatform

def combesExponent (P : PhysicalPlatform) : ℚ := P.bulkGap / (128 + 2*P.bulkGap)

theorem combesExponent_pos (P : PhysicalPlatform) : 0 < P.combesExponent :=
  div_pos P.bulkGap_pos (by have := P.bulkGap_pos; positivity)

def boundaryRate (P : PhysicalPlatform) : ℚ := 1 / (1 + P.combesExponent)

theorem boundaryRate_pos (P : PhysicalPlatform) : 0 < P.boundaryRate :=
  div_pos (by norm_num) (by have := P.combesExponent_pos; positivity)

theorem boundaryRate_lt_one (P : PhysicalPlatform) : P.boundaryRate < 1 := by
  have hp := P.combesExponent_pos
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem combesExponent_small (P : PhysicalPlatform) :
    16 * (Real.exp (2 * (P.combesExponent : ℝ)) - 1) ≤ (P.bulkGap : ℝ)/4 := by
  simpa only [combesExponent, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using
    rational_combes_small (P.bulkGap : ℝ) (by exact_mod_cast P.bulkGap_pos)

theorem boundaryRate_dominates (P : PhysicalPlatform) :
    Real.exp (-(P.combesExponent : ℝ)) ≤ (P.boundaryRate : ℝ) := by
  have hp : 0 < (P.combesExponent : ℝ) := by exact_mod_cast P.combesExponent_pos
  rw [Real.exp_neg]
  change (Real.exp (P.combesExponent : ℝ))⁻¹ ≤ ((1 / (1 + P.combesExponent) : ℚ) : ℝ)
  push_cast
  rw [one_div]
  apply inv_anti₀ (by positivity)
  simpa only [add_comm] using Real.add_one_le_exp (P.combesExponent : ℝ)

/-- A fixed coefficient; all input dependence is in `d*q+buffer+1`. -/
def boxCoefficient (P : PhysicalPlatform) : ℕ :=
  20 * (716 * coefficientSize P.basis + 1) + 40 * (SourceDefectLayout.radius P.defect + 2)

def volumeCoefficient (P : PhysicalPlatform) : ℚ := 3 * (P.boxCoefficient : ℚ)^3

theorem volumeCoefficient_nonneg (P : PhysicalPlatform) : 0 ≤ P.volumeCoefficient := by
  unfold volumeCoefficient
  positivity

theorem physical_side_feedback (P : PhysicalPlatform) (S : Source.SparseSystem)
    (precision d b : ℕ) (k : Direction) :
    Green.boxSide (DecoratedDefectLayout.physicalBox S precision P.basis P.defect d b) k ≤
      P.boxCoefficient * (d * SourceRouting.side S precision + b + 1) := by
  have hq := SourceRouting.side_pos S precision
  have he := DecoratedDefectLayout.source_extent_le S precision P.basis
  have hbase : Green.boxSide (DecoratedDefectLayout.baseBox S precision P.basis) k ≤
      (716 * coefficientSize P.basis + 1) * SourceRouting.side S precision := by
    fin_cases k <;> dsimp [Green.boxSide, DecoratedDefectLayout.baseBox, transformedBox] <;> nlinarith
  have hm := Nat.mul_le_mul_left (20*d) hbase
  change Green.boxSide (bufferedBox _ _ _ _) k ≤ _
  rw [bufferedBox_side]
  let A := 20 * (716 * coefficientSize P.basis + 1)
  let C := 40 * (SourceDefectLayout.radius P.defect + 2)
  have hC : 40 ≤ C := by dsimp [C]; omega
  change _ ≤ (A + C) * (d * SourceRouting.side S precision + b + 1)
  calc
    _ ≤ A * (d * SourceRouting.side S precision) + C + 40*b := by
      dsimp [A, C]
      nlinarith only [hm]
    _ ≤ (A+C) * (d * SourceRouting.side S precision) + (A+C) + (A+C)*b := by
      apply Nat.add_le_add
      · exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right A C)) (Nat.le_add_left C A)
      · exact Nat.mul_le_mul_right b (hC.trans (Nat.le_add_left C A))
    _ = _ := by ring

theorem physical_edge_feedback (P : PhysicalPlatform) (S : Source.SparseSystem)
    (precision d b : ℕ) :
    (Fintype.card (DecoratedDefectLayout.physicalBox S precision P.basis P.defect d b).Edge : ℝ) ≤
      (P.volumeCoefficient : ℝ) *
        ((d * SourceRouting.side S precision : ℕ) + (b : ℝ) + 1)^3 := by
  let box := DecoratedDefectLayout.physicalBox S precision P.basis P.defect d b
  let bound := P.boxCoefficient * (d * SourceRouting.side S precision + b + 1)
  have h0 := P.physical_side_feedback S precision d b 0
  have h1 := P.physical_side_feedback S precision d b 1
  have h2 := P.physical_side_feedback S precision d b 2
  change box.nx ≤ bound at h0
  change box.ny ≤ bound at h1
  change box.nz ≤ bound at h2
  have hvol : box.nx * box.ny * box.nz ≤ bound^3 := by
    calc
      _ ≤ bound * bound * bound := Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2
      _ = _ := by ring
  have ha : box.nx * (box.ny-1) * (box.nz-1) ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hb : (box.nx-1) * box.ny * (box.nz-1) ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hc : (box.nx-1) * (box.ny-1) * box.nz ≤ box.nx * box.ny * box.nz :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
  have hcard : Fintype.card box.Edge ≤ 3*bound^3 := by rw [retainedEdge_card]; omega
  have hR : (Fintype.card box.Edge : ℝ) ≤ (3*bound^3 : ℕ) := by exact_mod_cast hcard
  convert hR using 1
  simp only [volumeCoefficient, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, bound, Nat.cast_add, Nat.cast_one]
  ring

def chosenBuffer (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
    (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) : ℕ :=
  P.constants.buffer P.boundaryRate P.volumeCoefficient ζ S.nnz (d * SourceRouting.side S precision)
    P.boundaryRate_pos P.boundaryRate_lt_one P.volumeCoefficient_nonneg hζ hζ1

theorem chosenBuffer_error (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
    (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    let b := P.chosenBuffer S precision d ζ hζ hζ1
    let N := Fintype.card (DecoratedDefectLayout.physicalBox S precision P.basis P.defect d b).Edge
    2*(P.constants.detuningWidth ζ hζ : ℝ)/(P.bulkGap : ℝ)^2 +
      (4*(P.rowBound : ℝ)*(P.constants.backgroundInverseBudget ζ hζ S.nnz N : ℝ)/(P.bulkGap : ℝ)) *
        Real.exp (-(P.combesExponent : ℝ)*b) ≤ (ζ : ℝ)^2 := by
  dsimp only
  exact P.constants.buffer_error_bound P.boundaryRate P.volumeCoefficient ζ S.nnz
    (d * SourceRouting.side S precision) _ P.boundaryRate_pos P.boundaryRate_lt_one
    P.volumeCoefficient_nonneg hζ hζ1 (P.combesExponent : ℝ) P.boundaryRate_dominates
    (P.physical_edge_feedback S precision d _)

end PhysicalPlatform
end Maxwell.Composition
