import Maxwell.Composition.PhysicalFloor
import Maxwell.Composition.PhysicalGram
import Maxwell.Composition.SourceMediator
import Maxwell.Composition.SourceRecovery

/-! Exact rational parameter choices for the actual compiled source and
physical box. These formulas discharge the numerical hypotheses of the
physical Schur and inverse estimates before selecting a random draw. -/
namespace Maxwell.Composition.PhysicalParameters
open Maxwell.Logical Maxwell.Realization

/-- Routing width from the emitted sparse list length, without a semantic
finite-type cardinality operation. -/
def routingSide (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  Maxwell.Logical.Routing.portSide ((sourceCircuit S precision).size +
    (sourceCircuit S precision).size + (sourceSquareEntries S precision).length)

theorem routingSide_eq (S : Source.SparseSystem) (precision : ℕ) :
    routingSide S precision = SourceRouting.side S precision := by
  rw [SourceRouting.side,SourceEnumeration.vertex_count]
  rfl

/-- The routed inverse polynomial, evaluated with rational arithmetic. -/
def logicalInverseBudget (S : Source.SparseSystem) (precision : ℕ) (L : ℚ) : ℚ :=
  9*(1024*(routingSide S precision : ℚ))^2 *
    (256*L*((sourceCircuit S precision).size : ℚ)^4 + 1024*(routingSide S precision : ℚ))

theorem logicalInverseBudget_cast (S : Source.SparseSystem) (precision : ℕ) (L : ℚ) :
    (logicalInverseBudget S precision L : ℝ) = SourceMediator.inverseBudget S precision L := by
  simp [logicalInverseBudget, SourceMediator.inverseBudget, SourceSubdivision.ell, routingSide_eq]

theorem logicalInverseBudget_ge_one (S : Source.SparseSystem) (precision : ℕ)
    (L : ℚ) (hL : 1 ≤ L) : 1 ≤ logicalInverseBudget S precision L := by
  have h := SourceMediator.inverseBudget_ge_one S precision (L : ℝ) (by exact_mod_cast hL)
  rw [← logicalInverseBudget_cast] at h
  exact_mod_cast h

def spacingPlatform (P : PhysicalPlatform) : SpacingPlatform :=
  {P.spacing with minimumDistance := P.coreFloor}

def distance (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
    (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε) : ℕ :=
  (spacingPlatform P).spacing (logicalInverseBudget S precision L) ε
    (lt_of_lt_of_le zero_lt_one (logicalInverseBudget_ge_one S precision L hL)) hε

theorem distance_coreFloor (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
    (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε) :
    P.coreFloor ≤ distance P S precision L ε hL hε :=
  (spacingPlatform P).spacing_minimum _ _ _ _

theorem distance_minimum (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
    (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε) :
    P.spacing.minimumDistance ≤ distance P S precision L ε hL hε :=
  P.coreFloor_minimum.trans (distance_coreFloor P S precision L ε hL hε)

def zeta (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
    (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε) : ℚ :=
  P.spacing.zeta (distance P S precision L ε hL hε)

def alpha (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
    (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε) : ℚ :=
  P.spacing.alpha (distance P S precision L ε hL hε)

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision : ℕ)
variable (L ε : ℚ) (hL : 1 ≤ L) (hε : 0 < ε)

theorem zeta_pos : 0 < zeta P S precision L ε hL hε := P.spacing.zeta_pos _
theorem alpha_pos : 0 < alpha P S precision L ε hL hε := P.spacing.alpha_pos _

theorem zeta_le_half : zeta P S precision L ε hL hε ≤ 1/2 :=
  (spacingPlatform P).spacing_zeta_le_half _ _ _ _

theorem zeta_le_one : zeta P S precision L ε hL hε ≤ 1 :=
  (zeta_le_half P S precision L ε hL hε).trans (by norm_num)

theorem error_budget :
    P.spacing.errorConstant*(zeta P S precision L ε hL hε)^2 ≤
      alpha P S precision L ε hL hε*ε/(4096*logicalInverseBudget S precision L) :=
  (spacingPlatform P).spacing_error_budget _ _ _ _

theorem error_budget_real :
    (P.spacing.errorConstant : ℝ)*(zeta P S precision L ε hL hε : ℝ)^2 ≤
      (alpha P S precision L ε hL hε : ℝ)*(ε : ℝ)/
        (4096*SourceMediator.inverseBudget S precision L) := by
  rw [← logicalInverseBudget_cast]
  exact_mod_cast error_budget P S precision L ε hL hε

theorem zeta_sq_le_alpha (hε1 : ε ≤ 1) :
    (zeta P S precision L ε hL hε)^2 ≤ alpha P S precision L ε hL hε :=
  (spacingPlatform P).spacing_zeta_sq_le_alpha _ _
    (logicalInverseBudget_ge_one S precision L hL) hε hε1

/-- The anti-resonance inverse bound uses the entire actual finite edge set. -/
noncomputable def backgroundInverseBudget : ℚ :=
  P.constants.backgroundInverseBudget (zeta P S precision L ε hL hε)
    (zeta_pos P S precision L ε hL hε) S.nnz
    (Fintype.card (PhysicalGram.box P S precision (distance P S precision L ε hL hε)
      (zeta P S precision L ε hL hε) (zeta_pos P S precision L ε hL hε)
      (zeta_le_one P S precision L ε hL hε)).Edge)

theorem backgroundInverseBudget_ge_one (hm : 0 < S.nnz) :
    1 ≤ backgroundInverseBudget P S precision L ε hL hε := by
  have hτ := P.constants.detuningWidth_pos (zeta P S precision L ε hL hε) (zeta_pos P S precision L ε hL hε)
  have hτ1 := (P.constants.detuningWidth_bounds (zeta P S precision L ε hL hε)
    (zeta_pos P S precision L ε hL hε)).1
  unfold backgroundInverseBudget PhysicalConstants.backgroundInverseBudget
  apply (le_div_iff₀ hτ).mpr
  have hmQ : (1 : ℚ) ≤ S.nnz := by exact_mod_cast hm
  have hN : (0 : ℚ) ≤ Fintype.card
    (PhysicalGram.box P S precision (distance P S precision L ε hL hε)
      (zeta P S precision L ε hL hε) (zeta_pos P S precision L ε hL hε)
      (zeta_le_one P S precision L ε hL hε)).Edge := by positivity
  nlinarith

end Maxwell.Composition.PhysicalParameters
