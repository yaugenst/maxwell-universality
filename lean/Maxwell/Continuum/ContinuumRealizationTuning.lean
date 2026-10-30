import Maxwell.Continuum.ContinuumRealizationGeometry
import Maxwell.Continuum.FiniteAuxiliaryTargetBounds
import Maxwell.Continuum.FiniteAuxiliaryDyadic
import Maxwell.Composition.PhysicalDiagonal

/-! Literal rational coupling, diagonal, and reciprocal well strengths.
The only numerical input is a finite enclosure of each actual calibrated
quantity; all size and tuning conclusions follow from the selected tests. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition FiniteAuxiliary Auxiliary EffectiveMass
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput realMode muH

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
local instance tuningDecidableEq : DecidableEq (SourceIncidence.V S (precision p S hm)) := Classical.decEq _

def couplingValue (I : Fin 3 → Calibration.RationalInterval) (j : Fin 3) : ℚ :=
  -(couplingRound (zeta p S hm) (zeta_pos p S hm) (I j)).value

def targetDiagonal (I : Fin 3 → Calibration.RationalInterval) :
    SourceDecoration.Vertex S (precision p S hm) → ℚ :=
  PhysicalDiagonal.diagonal S (precision p S hm) (alpha p S hm) (couplingValue p S hm I)

def strengthData (μ : Calibration.RationalInterval) (I : Fin 3 → Calibration.RationalInterval)
    (i : SourceDecoration.Vertex S (precision p S hm)) :=
  onsiteRound (length p S hm) (length_pos p S hm) (zeta p S hm) (zeta_pos p S hm)
    μ (targetDiagonal p S hm I i)

def strength (μ : Calibration.RationalInterval) (I : Fin 3 → Calibration.RationalInterval)
    (i : SourceDecoration.Vertex S (precision p S hm)) : ℚ := (strengthData p S hm μ I i).value

variable {z : ℝ} (D : Auxiliary.Calibration (length p S hm : ℝ)⁻¹ z)

theorem coupling_error (I : Fin 3 → Calibration.RationalInterval)
    (hI : ∀ j, (I j).Contains (usefulCoupling (length_master p S hm) D (spacing p S hm) j))
    (hwidth : ∀ j, (I j).width ≤ (zeta p S hm)^2/16) (j : Fin 3) :
    |(couplingValue p S hm I j : ℝ)+usefulCoupling (length_master p S hm) D (spacing p S hm) j| ≤
      (zeta p S hm : ℝ)^2/16 := by
  have h := couplingRound_error (zeta p S hm) (zeta_pos p S hm) (I j) (hI j) (hwidth j)
  simpa only [couplingValue, Rat.cast_neg, neg_add_eq_sub, abs_sub_comm] using h

theorem coupling_upper (hb : S.source ≠ 0) (I : Fin 3 → Calibration.RationalInterval)
    (hI : ∀ j, (I j).Contains (usefulCoupling (length_master p S hm) D (spacing p S hm) j))
    (hwidth : ∀ j, (I j).width ≤ (zeta p S hm)^2/16) (j : Fin 3) :
    |(couplingValue p S hm I j : ℝ)| ≤ 2*Cs*(length p S hm : ℝ)^5*(zeta p S hm : ℝ) := by
  rw [zeta_cast]
  apply calibratedCoupling_upper (length_master p S hm) D (fun j => (couplingValue p S hm I j : ℝ))
  · intro k
    simpa only [← zeta_cast p S hm] using coupling_error p S hm D I hI hwidth k
  · simpa only [← zeta_cast p S hm] using single_interaction_tail p S hm hb

theorem useful_lower (hb : S.source ≠ 0) (j : Fin 3) :
    4*(alpha p S hm : ℝ) ≤ usefulCoupling (length_master p S hm) D (spacing p S hm) j := by
  have htail : Cs*(length p S hm : ℝ)^5*Real.exp (-cs*(length p S hm : ℝ)) ≤
      (cu/4)*(length p S hm : ℝ)^2*(8 : ℝ)^(-(spacing p S hm : ℝ)) := by
    rw [← alpha_cast]
    exact (single_interaction_tail p S hm hb).trans
      ((div_le_self (sq_nonneg _) (by norm_num)).trans (zeta_square_le_alpha p S hm))
  have h := usefulCoupling_lower (length_master p S hm) (length_even p S hm) D
    (spacing_bounds p S hm).1 (spacing_bounds p S hm).2.1 htail j
  rw [alpha_cast]
  convert h using 1
  ring

theorem coupling_lower (hb : S.source ≠ 0) (I : Fin 3 → Calibration.RationalInterval)
    (hI : ∀ j, (I j).Contains (usefulCoupling (length_master p S hm) D (spacing p S hm) j))
    (hwidth : ∀ j, (I j).width ≤ (zeta p S hm)^2/16) (j : Fin 3) :
    3*(alpha p S hm : ℝ) ≤ |(couplingValue p S hm I j : ℝ)| := by
  apply calibratedCoupling_lower (d := spacing p S hm) (length_master p S hm) D (alpha_pos p S hm)
    (budget_ge_one p S hm) (epsilon_le_one p S hm)
    (by simpa only [← zeta_cast p S hm] using (spacing_bounds p S hm).2.2.2.2)
    (fun j => (couplingValue p S hm I j : ℝ))
  · intro k
    simpa only [← zeta_cast p S hm] using coupling_error p S hm D I hI hwidth k
  · exact useful_lower p S hm D hb

theorem targetDiagonal_bound (hb : S.source ≠ 0) (I : Fin 3 → Calibration.RationalInterval)
    (hI : ∀ j, (I j).Contains (usefulCoupling (length_master p S hm) D (spacing p S hm) j))
    (hwidth : ∀ j, (I j).width ≤ (zeta p S hm)^2/16)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    |(targetDiagonal p S hm I i : ℝ)| ≤ (1/(2 : ℝ)^196)*(length p S hm : ℝ)^2 := by
  rw [targetDiagonal, PhysicalDiagonal.diagonal_cast]
  refine source_target_diagonal_bound S (precision p S hm) (d := spacing p S hm) (length_master p S hm)
    (alpha_pos p S hm) (spacing_bounds p S hm).2.2.1 (budget_ge_one p S hm) (epsilon_le_one p S hm)
    (by simpa only [← zeta_cast p S hm] using (spacing_bounds p S hm).2.2.2.2)
    (fun j => (couplingValue p S hm I j : ℝ)) ?_ i
  intro j
  simpa only [← zeta_cast p S hm] using coupling_upper p S hm D hb I hI hwidth j

theorem strength_bounds (hb : S.source ≠ 0) (μ : Calibration.RationalInterval)
    (I : Fin 3 → Calibration.RationalInterval)
    (hμ : μ.Contains (muH D (inverse_length_le_1024 (length_master p S hm))))
    (hwμ : μ.width ≤ (zeta p S hm)^2/8)
    (hI : ∀ j, (I j).Contains (usefulCoupling (length_master p S hm) D (spacing p S hm) j))
    (hwI : ∀ j, (I j).width ≤ (zeta p S hm)^2/16)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    0 < strength p S hm μ I i ∧
    (strength p S hm μ I i : ℝ) ≤ (2 : ℝ)^130*(length p S hm : ℝ)⁻¹^2 ∧
    |(strength p S hm μ I i : ℝ)⁻¹-
      (muH D (inverse_length_le_1024 (length_master p S hm))+(targetDiagonal p S hm I i : ℝ))| ≤
        (zeta p S hm : ℝ)^2 :=
  onsiteRound_bounds (length_master p S hm) D (length_pos p S hm) (zeta p S hm)
    (zeta_pos p S hm) (zeta_le_one p S hm) μ (targetDiagonal p S hm I i) hμ hwμ
    (targetDiagonal_bound p S hm D hb I hI hwI i)

theorem strength_budget_le_one : (2 : ℝ)^130*(length p S hm : ℝ)⁻¹^2 ≤ 1 := by
  have hi : (length p S hm : ℝ)⁻¹ ≤ ((2 : ℝ)^65)⁻¹ :=
    inverse_length_le_power (length_master p S hm) (by have := exponent_large; omega)
  have hs := pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) hi 2
  have hh := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2^130 by positivity)
  apply hh.trans_eq
  rw [inv_pow, ← pow_mul, show 65*2 = (130 : ℕ) by omega, mul_inv_cancel₀ (by positivity)]

#print axioms useful_lower
#print axioms coupling_lower
#print axioms strength_bounds

end Maxwell.Continuum.RealizationParameters
