import Maxwell.Continuum.ParameterDyadic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Literal even side lengths and the continuum eigenvalue-count budget.
Only three side lengths are computed, never an ambient mesh or matrix. -/

namespace Maxwell.Continuum.Parameters

open scoped BigOperators
set_option maxRecDepth 4096

def boxSide (s : Fin 3 → ℕ) (L t : ℕ) (j : Fin 3) : ℕ := 2*(s j+L+L*t+4)

def boxCount (s : Fin 3 → ℕ) (L t : ℕ) : ℕ := 2*∏ j, (1+2*boxSide s L t j)

theorem boxSide_even (s : Fin 3 → ℕ) (L t : ℕ) (j : Fin 3) : Even (boxSide s L t j) :=
  ⟨s j+L+L*t+4, by unfold boxSide; omega⟩

theorem boxSide_margin (s : Fin 3 → ℕ) (L t : ℕ) (j : Fin 3) :
    2*s j+2*(L+L*t+4) = boxSide s L t j := by unfold boxSide; ring

theorem boxCount_pos (s : Fin 3 → ℕ) (L t : ℕ) : 0 < boxCount s L t := by
  unfold boxCount
  exact Nat.mul_pos (by decide) (Finset.prod_pos (fun _ _ => by omega))

theorem boxCount_growth (s : Fin 3 → ℕ) (L t : ℕ) :
    boxCount s L t ≤ boxCount s L 0*(1+t)^3 := by
  have hfactor (j : Fin 3) : 1+2*boxSide s L t j ≤ (1+2*boxSide s L 0 j)*(1+t) := by
    unfold boxSide
    nlinarith
  calc
    boxCount s L t ≤ 2*∏ j, ((1+2*boxSide s L 0 j)*(1+t)) :=
      Nat.mul_le_mul_left _ (Finset.prod_le_prod (fun j _ => hfactor j))
    _ = boxCount s L 0*(1+t)^3 := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, boxCount]
      ring

/-- Exact rational detuning and total-error budgets at each candidate box. -/
def inverseBudget (m N : ℕ) (τ : ℚ) : ℚ := 64*(m : ℚ)*N/τ

def errorBudget (m N : ℕ) (ε τ : ℚ) : ℚ := ε/(2^27*inverseBudget m N τ)

def globalBudget (e J m N L d : ℕ) (K : ℚ) : ℚ :=
  ((2 : ℚ)^e)^32*(1+(N : ℚ))^2*(1+(J : ℚ)+m)^2*(1+K)^4*
    (1+(alpha L d)⁻¹)^2*(L : ℚ)^100

def stoppingRatio (e J m N L d : ℕ) (K ε τ : ℚ) : ℚ :=
  4*globalBudget e J m N L d K/errorBudget m N ε τ

theorem inverseBudget_pos {m N : ℕ} {τ : ℚ}
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) : 0 < inverseBudget m N τ := by
  unfold inverseBudget
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  positivity

theorem errorBudget_pos {m N : ℕ} {ε τ : ℚ}
    (hm : 0 < m) (hN : 0 < N) (hε : 0 < ε) (hτ : 0 < τ) :
    0 < errorBudget m N ε τ := by
  have hi := inverseBudget_pos hm hN hτ
  unfold errorBudget
  positivity

theorem globalBudget_nonneg (e J m N L d : ℕ) (K : ℚ) :
    0 ≤ globalBudget e J m N L d K := by unfold globalBudget; positivity

theorem stoppingRatio_formula (e J m N L d : ℕ) (K ε τ : ℚ) :
    stoppingRatio e J m N L d K ε τ =
      (2 : ℚ)^35*((2 : ℚ)^e)^32*(m : ℚ)*N*(1+(N : ℚ))^2*
      (1+(J : ℚ)+m)^2*(1+K)^4*(1+(alpha L d)⁻¹)^2*(L : ℚ)^100/(τ*ε) := by
  have halg (X M N ε τ : ℚ) :
      4*X/(ε/(2^27*(64*M*N/τ))) = (2 : ℚ)^35*M*N*X/(τ*ε) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [stoppingRatio, errorBudget, inverseBudget, halg, globalBudget]
  congr 1
  ac_rfl

/-- All dependence of the actual stopping ratio on the candidate buffer is
bounded by the ninth power, with its literal value at zero as coefficient. -/
theorem stoppingRatio_growth (e J m L d : ℕ) (s : Fin 3 → ℕ) (K ε τ : ℚ)
    (hε : 0 < ε) (hτ : 0 < τ) (t : ℕ) :
    stoppingRatio e J m (boxCount s L t) L d K ε τ ≤
      stoppingRatio e J m (boxCount s L 0) L d K ε τ*(1+(t : ℚ))^9 := by
  have hN : (boxCount s L t : ℚ) ≤ (boxCount s L 0 : ℚ)*(1+(t : ℚ))^3 := by
    exact_mod_cast boxCount_growth s L t
  have hP : (1 : ℚ) ≤ (1+(t : ℚ))^3 :=
    one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg t))
  have hN1 : 1+(boxCount s L t : ℚ) ≤
      (1+(boxCount s L 0 : ℚ))*(1+(t : ℚ))^3 := by nlinarith
  have hmul := mul_le_mul hN (pow_le_pow_left₀ (by positivity) hN1 2)
    (by positivity : (0 : ℚ) ≤ (1+(boxCount s L t : ℚ))^2) (by positivity)
  let C : ℚ := (2 : ℚ)^35*((2 : ℚ)^e)^32*(m : ℚ)*
      (1+(J : ℚ)+m)^2*(1+K)^4*(1+(alpha L d)⁻¹)^2*(L : ℚ)^100/(τ*ε)
  have hC : 0 ≤ C := by unfold C; positivity
  have hg := mul_le_mul_of_nonneg_left hmul hC
  rw [stoppingRatio_formula, stoppingRatio_formula]
  convert hg using 1 <;> dsimp only [C] <;> ring

theorem stoppingRatio_test {e J m N L d t : ℕ} {K ε τ : ℚ}
    (hm : 0 < m) (hN : 0 < N) (hε : 0 < ε) (hτ : 0 < τ)
    (h : stoppingRatio e J m N L d K ε τ*rationalDecay t ≤ 1) :
    globalBudget e J m N L d K*rationalDecay t ≤ errorBudget m N ε τ/4 := by
  have he := errorBudget_pos hm hN hε hτ
  unfold stoppingRatio at h
  have hh := (div_le_iff₀ he).mp (show
    (4*globalBudget e J m N L d K*rationalDecay t)/errorBudget m N ε τ ≤ 1 by
      simpa only [div_mul_eq_mul_div] using h)
  linarith

#print axioms stoppingRatio_growth

end Maxwell.Continuum.Parameters
