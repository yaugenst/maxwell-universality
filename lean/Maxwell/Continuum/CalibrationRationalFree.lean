import Maxwell.Continuum.CalibrationFreeRounding
import Maxwell.Continuum.CalibrationPi

/-! Executable rational entries of all three free inverse polarizations
and the complete noncentral lattice gap. No truncation in alias index
is used in the matrix soundness or uniform norm statements. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber Maxwell.Certificate Elementary

noncomputable def gridDirection (r : Fin 3 → ℝ) (ν : Alias) : Fin 3 → ℝ :=
  fun j => (ν j : ℝ)+1/2+r j

theorem gridDirection_noncentral (r : Fin 3 → ℝ) (hr : ∀ j, |r j| ≤ 1/16)
    (ν : Alias) (hν : ¬IsCentralAlias ν) : 2 ≤ directionSquare (gridDirection r ν) := by
  obtain ⟨j, hj⟩ : ∃ j, ν j ≠ -1 ∧ ν j ≠ 0 := by
    simpa only [IsCentralAlias, not_forall, not_or] using hν
  have hjcase : ν j ≤ -2 ∨ 1 ≤ ν j := by omega
  have hbound : (529/256 : ℝ) ≤ (gridDirection r ν j)^2 := by
    have hrj := abs_le.mp (hr j)
    rcases hjcase with hn | hn
    · have hn' : (ν j : ℝ) ≤ -2 := by exact_mod_cast hn
      have hval : gridDirection r ν j ≤ -23/16 := by unfold gridDirection; linarith
      nlinarith [sq_nonneg (gridDirection r ν j+23/16)]
    · have hn' : (1 : ℝ) ≤ ν j := by exact_mod_cast hn
      have hval : 23/16 ≤ gridDirection r ν j := by unfold gridDirection; linarith
      nlinarith [sq_nonneg (gridDirection r ν j-23/16)]
  have hsum : (gridDirection r ν j)^2 ≤ directionSquare (gridDirection r ν) :=
    Finset.single_le_sum (f := fun k => (gridDirection r ν k)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  linarith

def rationalDirection (r : Fin 3 → ℚ) (ν : Alias) : Fin 3 → ℚ :=
  fun j => (ν j : ℚ)+1/2+r j

def rationalInverseMatrix (t E : ℚ) (a : Fin 3 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  (t^2*(∑ j, a j^2)-E)⁻¹ • (1-E⁻¹ • Matrix.vecMulVec (fun j => t*a j) (fun j => t*a j))

theorem rationalInverseMatrix_sound (t E : ℚ) (a : Fin 3 → ℚ) :
    (rationalInverseMatrix t E a).map (Rat.castHom ℂ) =
      inverseMatrix (realMomentum (fun j => (t : ℝ)*(a j : ℝ))) (E : ℂ) := by
  ext i j
  change ((rationalInverseMatrix t E a i j : ℚ) : ℂ) = _
  simp only [rationalInverseMatrix, inverseMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, momentumSquare, momentumOuter, realMomentum,
    smul_eq_mul, Rat.cast_mul, Rat.cast_sub, Rat.cast_inv,
    Rat.cast_pow, Rat.cast_sum, Complex.ofReal_mul, Complex.ofReal_ratCast,
    Matrix.one_apply]
  split_ifs <;> push_cast <;> simp only [mul_pow, ← Finset.mul_sum]

def rationalCentralCheck (ν : Alias) : Bool := decide (∀ j, ν j = -1 ∨ ν j = 0)

theorem rationalCentralCheck_true (ν : Alias) : rationalCentralCheck ν = true ↔ IsCentralAlias ν := by
  simp only [rationalCentralCheck, decide_eq_true_eq, IsCentralAlias]

def rationalFreeInverseMatrix (t E : ℚ) (r : Fin 3 → ℚ) (ν : Alias) : Matrix (Fin 3) (Fin 3) ℚ :=
  if rationalCentralCheck ν then 1 else rationalInverseMatrix t E (rationalDirection r ν)

theorem rationalDirection_cast (r : Fin 3 → ℚ) (ν : Alias) :
    (fun j => ((rationalDirection r ν j : ℚ) : ℝ)) = gridDirection (fun j => (r j : ℝ)) ν := by
  funext j
  simp only [rationalDirection, gridDirection, Rat.cast_add, Rat.cast_intCast, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat]

def piCenter (P : ℕ) : ℚ := (piApprox (P+6)).center

theorem piCenter_error (P : ℕ) : |Real.pi-(piCenter P : ℝ)| ≤ (1/2 : ℝ)^(P+6) := by
  have h := piApprox_contains (P+6)
  change |Real.pi-(piCenter P : ℝ)| ≤ ((piApprox (P+6)).radius : ℝ) at h
  rw [piApprox_radius] at h
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem piCenter_bounds (P : ℕ) : (3 : ℝ) ≤ piCenter P ∧ (piCenter P : ℝ) ≤ 4 := by
  have h := abs_le.mp (piCenter_error P)
  have hp : (1/2 : ℝ)^(P+6) ≤ (1/2 : ℝ)^6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at hp
  constructor <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

#print axioms rationalInverseMatrix_sound
#print axioms gridDirection_noncentral

end Maxwell.Continuum.Calibration
