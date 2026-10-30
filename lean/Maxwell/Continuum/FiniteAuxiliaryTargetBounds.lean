import Maxwell.Continuum.FiniteAuxiliarySourceTarget
import Maxwell.Continuum.FiniteAuxiliaryCoupling
import Maxwell.Continuum.ParameterTuning

/-! Actual coupling calibration and the diagonal range required by the
continuum reciprocal tuning rule. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] realMode Cs

theorem usefulCoupling_abs_upper {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (d : ℕ) (j : Fin 3) :
    |usefulCoupling hL D d j| ≤ Cs*(L : ℝ)^5*
      (((3 : ℝ)^d)⁻¹+Real.exp (-cs*(L : ℝ))) := by
  have he := usefulCoupling_real hL D d j
  have hi := norm_inner_le_norm (𝕜 := ℂ) (realMode D (inverse_length_le_1024 hL))
    (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)
      (realMode D (inverse_length_le_1024 hL)))
  rw [he, Complex.norm_real, Real.norm_eq_abs, realMode_norm, one_mul] at hi
  have hn := (physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)).le_opNorm
    (realMode D (inverse_length_le_1024 hL))
  rw [realMode_norm, mul_one] at hn
  have hunit : latticeOneNorm (Pi.single j (1 : ℤ)) = 1 := by
    classical
    fin_cases j <;> norm_num [latticeOneNorm, Fin.sum_univ_succ, Pi.single_apply]
  exact (hi.trans hn).trans (by
    simpa only [hunit, mul_one] using
      (physicalWellBlock_norm hL D le_rfl (by positivity) d (Pi.single j 1)))

private theorem calibrated_size {A ζ b c : ℝ} (hA : 1 ≤ A) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hc : |c| ≤ A*ζ+ζ^2/4) (hb : |b+c| ≤ ζ^2/16) : |b| ≤ 2*A*ζ := by
  have ht : |b| ≤ |b+c|+|c| := by
    simpa only [add_sub_cancel_right, sub_zero, zero_sub, abs_neg] using abs_sub_le (b+c) 0 c
  have hm : ζ ≤ A*ζ := le_mul_of_one_le_left hζ hA
  nlinarith only [ht, hc, hb, hm, hζ, hζ1]

theorem calibratedCoupling_upper {L d : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (β : Fin 3 → ℝ)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (htail : Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4) :
    ∀ j, |β j| ≤ 2*Cs*(L : ℝ)^5*((3 : ℝ)^d)⁻¹ := by
  intro j
  have hA : 1 ≤ Cs*(L : ℝ)^5 :=
    one_le_mul_of_one_le_of_one_le Cs_ge_one (one_le_pow₀ (length_ge_one hL))
  have hz : ((3 : ℝ)^d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hu : |usefulCoupling hL D d j| ≤ Cs*(L : ℝ)^5*((3 : ℝ)^d)⁻¹+(((3 : ℝ)^d)⁻¹)^2/4 := by
    have he := usefulCoupling_abs_upper hL D d j
    rw [mul_add] at he
    exact he.trans (add_le_add le_rfl htail)
  have he := calibrated_size hA (by positivity) hz hu (hβ j)
  convert he using 1
  ring

theorem calibratedCoupling_lower {L d : ℕ} {z α K ε : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hα : 0 < α) (hK : 1 ≤ K) (hε : ε ≤ 1)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (β : Fin 3 → ℝ)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (hlower : ∀ j, 4*α ≤ usefulCoupling hL D d j) :
    ∀ j, 3*α ≤ |β j| := by
  have hsmall := Parameters.second_test_zeta hL hα hK hε hsecond
  intro j
  have he := (abs_le.mp (hβ j)).2
  have hn := neg_le_abs (β j)
  linarith only [hsmall, he, hn, hlower j]

variable (S : Source.SparseSystem) (precision : ℕ)
local instance targetBoundsDecidableEq : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem source_target_diagonal_bound {L d : ℕ} {α K ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K) (hε : ε ≤ 1)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (β : Fin 3 → ℝ) (hβ : ∀ j, |β j| ≤ 2*Cs*(L : ℝ)^5*((3 : ℝ)^d)⁻¹)
    (i : SourceDecoration.Vertex S precision) :
    |(SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i| ≤
      (1/(2 : ℝ)^196)*(L : ℝ)^2 := by
  cases i with
  | inl v =>
    simp only [SignedIncidence.targetMatrix, Matrix.fromBlocks_apply₁₁,
      SignedIncidence.terminalDiagonal, Matrix.diagonal_apply_eq, abs_mul, abs_of_pos hα]
    have hdeg0 : 0 ≤ (SourceIncidence.graph S precision).degree v :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hdiag := SourceSubdivision.diagonal_abs_le_three S precision v
    have hdeg := SourceIncidence.degree_le_three S precision v
    have ha := abs_sub_le (SourceMediator.diagonal S precision v) 0
      ((SourceIncidence.graph S precision).degree v)
    rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg hdeg0] at ha
    have hab : |SourceMediator.diagonal S precision v-(SourceIncidence.graph S precision).degree v| ≤ 6 := by
      change |SourceMediator.diagonal S precision v| ≤ 3 at hdiag
      linarith only [ha, hdiag, hdeg]
    exact ((mul_le_mul_of_nonneg_left hab hα.le).trans
      (by nlinarith only [hα1] : α*6 ≤ 6)).trans (Parameters.terminal_budget hL)
  | inr e =>
    simp only [SignedIncidence.targetMatrix, Matrix.fromBlocks_apply₂₂,
      SignedIncidence.mediatorDiagonal, Matrix.diagonal_apply_eq,
      abs_div, abs_neg, abs_pow, sq_abs, abs_of_pos hα]
    exact Parameters.mediator_square_budget hL hα hK hε hsecond (hβ (SourceIncidence.axis S precision e))

#print axioms usefulCoupling_abs_upper
#print axioms source_target_diagonal_bound

end Maxwell.Continuum.FiniteAuxiliary
